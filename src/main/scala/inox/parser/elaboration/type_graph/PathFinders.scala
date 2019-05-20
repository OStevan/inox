package inox.parser.elaboration.type_graph

import scala.collection.mutable

trait PathFinders { self: GraphStructure =>

  /**
    * Class representing a path found by path finders
    * @param edges constructing a path
    * @param finder used to generate the path
    */
  class GraphPath (val edges: Array[Edge], val finder: PathFinder) {
    assert(edges.length != 0, "Path should have some edges connecting the two ")

    /**
      * increment the counter of the successful paths
      * @return
      */
    def incSatisfiableCount(): Unit = {
      var edgeSet: Set[Edge] = Set.empty
      var nodeSet: Set[Node] = Set.empty

      firstInPath().incSatisfiableCount()

      nodeSet = nodeSet + firstInPath()

      for (k <- edges.indices) {
        if (!edgeSet.contains(edges(k))) {
          edges(k).incSatisfiableCount()
          edgeSet = edgeSet + edges(k)
        }
        if (!nodeSet.contains(edges(k).to())) {
          edges(k).to().incSatisfiableCount()
          nodeSet += edges(k).to()
        }
      }
    }

    /**
      * TODO maybe change this to be more generic?
      * Checks of from is less or equal to to structurally, without any prior knowledge
      * @param from
      * @param to
      * @return
      */
    private def leq(from: Node, to: Node): Boolean = {
      if (from == to)
        return true

      if (from.isTrivialEnd || to.isTrivialEnd)
        return true

      false
    }

    /**
      * Method to get the first element in a path
      * @return node representing the start of the path
      */
    def firstInPath(): Node = edges(0).from()

    /**
      * Method to get the last element of the path
      * @return nore representing the end node of the path
      */
    def lastInPath(): Node = edges(edges.length - 1).to()

    private def satisfiable(from: Node, to: Node): Boolean = {


      // TODO finish this
      if (from == to)
        return true

      // TODO add for constructors

      if (leq(from, to))
        return true


      false
    }

    /**
      * checks if the path is satisfiable having the constraint in mind
      * @return
      */
    def isSatisfiablePath: Boolean = {
      if (edges.length == 0)
        return false
      satisfiable(firstInPath(), lastInPath())
    }

    /**
      * Checks if a relation is derivable
      * @return
      */
    def isValidPath: Boolean = {

      if (edges.length == 0)
        return false

      if (firstInPath() ==  lastInPath())
        return true

      leq(firstInPath(), lastInPath())
    }

    /**
      * if the path is unsatisfiable mark path as contributing
      * @return
      */
    def markCause() = {
      // TODO add marking cause
    }

    /**
      * Checks if the path is satisfiable
      * @return
      */
    def isUnsatisfiable: Boolean = {
      if (edges.length == 0)
        return false

      !isSatisfiablePath
    }

    /**
      * Checks if the edge is informative based on the explanation from the paper
      * @return
      */
    def isInformative: Boolean = {
      //    When either end node of a satisfiable LEQ edge is an unification variable, its satisfi-
      //    ability is trivial and hence not informative for error diagnosis. Also uninformative is an LEQ edge derived
      //    from unsatisfiable edges. Only the informative edges are used for error diagnosis.

      if (edges.length == 0)
        return false

      if (firstInPath() == lastInPath())
        return false


      // add a check if an node is added during graph saturation if it is then a path is not informative

      val leqElements: mutable.Stack[Node] = mutable.Stack()
      val length = 0
      val firstNode = firstInPath()
      leqElements.push(firstNode)

      for (edge <- edges) {
        if (!edge.to().isTrivialEnd) {

          // there are still non processed nodes
          if (leqElements.nonEmpty &&
            // path until here is not satisfiable
            // TODO see how to change this
            !satisfiable(leqElements.top, edge.to()) &&
            // we have reached the same element from were we started
            // edge from is the same as edge to
            !(leqElements.top == firstInPath()) && edge.to() == lastInPath())
            return false
          else if (!edge.to().hasVars) {
            leqElements.pop()
            leqElements.push(edge.to())
          }
        }
      }
      // passes the check
      true
    }


    def pathNodes(): Seq[Node] = {
      var nodes: Set[Node] = Set.empty
      for (edge <- edges) {
        nodes = nodes + edge.from()
        nodes = nodes + edge.to()
      }

      nodes.toSeq
    }

  }

  /**
    * Generic path finder
    */
  trait PathFinder {
    def graph: Graph

    protected trait ReductionEdge extends Edge

    protected case class LessEqual(from: Node, to: Node, size: Int) extends ReductionEdge

    def getPath(from: Node, to: Node): List[Edge]

    def hasLeqEdge(start: Node, end: Node): Boolean
  }

  /**
    * Finds context free language reachable paths
    */
  abstract class CFLPathFinder extends PathFinder {

    protected class Evidence(val from: Node, val to: Node)


    var graph: Graph = _
    protected val nextHop: mutable.Map[Node, mutable.Map[Node, List[Evidence]]] = mutable.Map()
    private val inferredLR: mutable.Map[Node, mutable.Set[Node]] = mutable.Map()

    def this(graph: Graph) = {
      this()
      this.graph = graph
    }

    def inferLeqEdge(from: Node, to: Node, length: Int, evidence: List[Evidence], atomic: Boolean)

    protected def addNextHop(start: Node, end: Node, evidence: List[Evidence]): Unit = {
      nextHop.getOrElseUpdate(start, mutable.Map[Node, List[Evidence]]()).getOrElseUpdate(end, evidence)
    }

    protected def hasNextHop(start: Node, end: Node): Boolean = {
      nextHop.getOrElse(start, mutable.Map[Node, List[Evidence]]()).contains(end)
    }

    protected def getNextHop(start: Node, end: Node): List[Evidence] = {
      nextHop.getOrElse(start, mutable.Map()).getOrElse(end, List())
    }

    protected def addAtomicLeqEdge(from: Node, to: Node): Unit = {
      inferredLR.getOrElseUpdate(from, new mutable.HashSet[Node]()).add(to)
    }

    protected def hasAtomicEdge(from: Node, to: Node): Boolean = {
      inferredLR.getOrElseUpdate(from, new mutable.HashSet[Node]()).contains(to)
    }

    override def getPath(from: Node, to: Node): List[Edge] = {
      getLeqPath(from, to)
    }

    protected def getLeqPath(from: Node, to: Node): List[Edge] = {
      val evidence = getNextHop(from, to)

      if (evidence.isEmpty) {
        val edge: Edge = getOriginalEdge(from, to)
        if (edge == null) {
          assert(assertion = false, "Found a path without a original edge")
          List()
        } else
          List(edge)
      } else {
        evidence.foldLeft(List[Edge]()) {
          case (extracted, evi) => extracted ++ getLeqPath(evi.from, evi.to)
        }
      }
    }


    protected def getOriginalEdge(from: Node, to: Node): Edge = {
      val edges = graph.nodeEdgesMap.getOrElse(from, Set())
      for (edge <- edges)
        if (edge.to() == to)
          return edge
      null
    }
  }


  /**
    * Finds shortest paths
    */
  class ShortestPathFinder(graph: Graph) extends CFLPathFinder(graph) {

    private val INFINITY = Int.MaxValue
    val shortestLEQPaths = new mutable.HashMap[Node, mutable.Map[Node, Int]]()
    val queue: mutable.Queue[ReductionEdge] = mutable.Queue[ReductionEdge]()

    init()
    saturation()



    def init(): Unit = {
      for (edge <- graph.edges) {
        shortestLEQPaths.update(edge.from(), shortestLEQPaths.getOrElse(edge.from(), new mutable.HashMap[Node, Int]()).updated(edge.to(), 1))
        inferLeqEdge(edge.from(), edge.to(), 1, List(), atomic = true)
      }

      // temp solution, counting on the fact that we are only using leq edges
      queue ++= graph.edges.map {
        case a: Edges.LessEqualEdge => LessEqual(a.from, a.to, 1)
      }
    }

    //  def getPathSize(from: Node, to: Node): Int = {
    //    shortestLEQPaths.getOrElse(from, new mutable.HashMap[Node, Int]()).getOrElse(to, INFINITY)
    //  }
    //
    //  def findShortestPaths() = {
    //    val workList = mutable.Queue[Edge]() ++ graph.edges
    //    while (workList.nonEmpty) {
    //      val currentEdge = workList.dequeue()
    //      for (connectingEdge <- graph.nodeEdgesMap.getOrElse(currentEdge.to(), Set())) {
    //        val newPathSize = getPathSize(currentEdge.from(), currentEdge.to()) + getPathSize(connectingEdge.from(), connectingEdge.to())
    //        if (newPathSize < getPathSize(currentEdge.from(), connectingEdge.to())) {
    //          shortestLEQPaths.update(currentEdge.from(), shortestLEQPaths.getOrElse(currentEdge.from(), new mutable.HashMap[Node, Int]()).updated(connectingEdge.to(), 1))
    //        }
    //      }
    //    }
    //  }

    // edge inference
    override def inferLeqEdge(from: Node, to: Node, length: Int, evidence: List[Evidence], atomic: Boolean): Unit = {
      addNextHop(from, to, evidence)
      if (from == to)
        return
      queue.enqueue(LessEqual(from, to, length))
      setShortestLeq(from, to, length)
      if (atomic)
        addAtomicLeqEdge(from, to)
    }

    // LEQ shortest path helpers

    /**
      * length of the currently found shortest path
      * @param start node of the path
      * @param end node of the path
      * @return length of the path or <code>INFINITY</code> if the path does not exist
      */
    private def getShortestLeq(start: Node, end: Node): Int =
      shortestLEQPaths.getOrElse(start, mutable.Map[Node, Int]()).getOrElse(end, INFINITY)

    /**
      * sets the new shortest path size between the two nodes
      * @param start node of the path
      * @param end node of the path
      * @param length length of the path connecting the two
      */
    private def setShortestLeq(start: Node, end: Node, length: Int): Unit =
      shortestLEQPaths.getOrElseUpdate(start, mutable.Map[Node, Int]()).update(end, length)

    // CFG shortest path rules
    /**
      * apply rule LEQ = LEQ LEQ
      *
      * @param from node of the new edge
      * @param mid node connecting the two existing edges
      * @param to node edging the new edge
      */
    private def ruleLeqLeq(from: Node, mid: Node, to: Node): Unit = {
      if (from == to)
        return
      val leftDistance = getShortestLeq(from, mid)
      val rightDistance = getShortestLeq(mid, to)
      val currentDistance = getShortestLeq(from, to)

      if (leftDistance == INFINITY || rightDistance == INFINITY)
        return
      if (leftDistance + rightDistance < currentDistance) {
        setShortestLeq(from, to, leftDistance + rightDistance)
        inferLeqEdge(from, to, leftDistance + rightDistance, List(new Evidence(from, mid), new Evidence(mid, to)),atomic = false)
      }

    }

    def saturation(): Unit = {
      val allNodes = graph.nodes

      //    var processedLenghts = 0

      while (queue.nonEmpty) {
        val edge = queue.dequeue()

        // tryAddingExtraEdges, without constructors

        for (node <- allNodes) {
          edge match {
            case LessEqual(from, to, size) =>
              if (hasAtomicEdge(to, node))
                ruleLeqLeq(from, to, node)
              if (hasAtomicEdge(node, from))
                ruleLeqLeq(node, from, to)
          }
        }
      }

    }

    override def hasLeqEdge(start: Node, end: Node): Boolean = getShortestLeq(start, end) != INFINITY
  }

}