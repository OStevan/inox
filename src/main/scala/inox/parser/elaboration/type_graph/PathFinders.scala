package inox.parser.elaboration.type_graph

import inox.parser.elaboration.{Constraints, SimpleTypes}

import scala.collection.mutable

trait PathFinders { self: GraphStructure with Constraints with SimpleTypes=>

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
      if (from entityInformationEquality  to)
        return true

      if (from.isTrivialEnd || to.isTrivialEnd)
        return true

      to.accept(from)
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
      if (from entityInformationEquality   to)
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

      if (firstInPath() entityInformationEquality lastInPath())
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

      if (firstInPath() entityInformationEquality lastInPath())
        return false

      if (lastInPath() accept firstInPath())
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
            !(leqElements.top == firstInPath()) && (edge.to() ==  lastInPath()))
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

    /**
      * LEQ := LEQ LEQ
      * LEQ := LEFT RIGHT (rule give rise to cyclic paths which are ignored)
      * @param from node
      * @param to node
      * @param length of edge
      */
    protected case class LessEqual(from: Node, to: Node, length: Int) extends ReductionEdge

    /**
      * LEFT := original
      * LEFT := LEFT LEQ (position is inherited from the child LEFT)
      * @param from node
      * @param to node
      * @param position position in constructor
      * @param length of the edge
      */
    protected case class LeftEdge(from: Node, to: Node, position: Int, length: Int) extends ReductionEdge

    /**
      * RIGHT := decompositional
      * RIGHT := LEQ RIGHT (position is inherited from the child right)
      * @param from node
      * @param to node
      * @param position position in the constructor
      * @param size
      */
    protected case class RightEdge(from: Node, to: Node, position: Int, size: Int) extends ReductionEdge

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
  class ShortestPathFinder(g: Graph) extends CFLPathFinder(g) {

    private val INFINITY = Int.MaxValue
    private val shortestLEQPaths = new mutable.HashMap[Node, mutable.Map[Node, Int]]()

    // used for expanding
    private var constructorNodes: Map[Node, List[Node]] = Map.empty
    private var trace: Map[Node, Set[Edge]] = Map.empty


    /**
      * map from node to map of node to map of position to length
      */
    val shortestLeftPaths = new mutable.HashMap[Node, mutable.Map[Node, mutable.Map[Int, Int]]]()
    val queue: mutable.Queue[ReductionEdge] = mutable.Queue[ReductionEdge]()

    var rightEdges: Map[Node, Map[Node, Int]] = Map.empty

    init()
    saturation()



    def init(): Unit = {
      graph.edges.foreach {
        case a: Edges.LessEqualEdge =>
          inferLeqEdge(a.from, a.to, 1, List.empty, atomic = true)
        case Edges.ConstructorEdge(from, to, Edges.ConstructorEdgeDirection.Original, position) =>
          inferLeftEdge(from, to, 1, List.empty, position, atomic = true)
        case Edges.ConstructorEdge(from, to, Edges.ConstructorEdgeDirection.Decompositional, position) =>
          insertRightEdge(to, from, position)
      }
    }


    // edge inference
    override def inferLeqEdge(from: Node, to: Node, length: Int, evidence: List[Evidence], atomic: Boolean): Unit = {
      addNextHop(from, to, evidence)
      if (from entityInformationEquality to)
        return
      queue.enqueue(LessEqual(from, to, length))
      setShortestLeq(from, to, length)
      if (atomic)
        addAtomicLeqEdge(from, to)
    }

    def inferLeftEdge(from: Node, to: Node, length: Int, list: List[Evidence], position: Int, atomic: Boolean): Unit = {
      queue.enqueue(LeftEdge(from, to, position, length))
      setShortestLeft(from, to, position, length)
    }

    /**
      * Not the best solution
      */
    def insertRightEdge(from: Node, to: Node, position: Int): Unit = {
      rightEdges = rightEdges.updated(from, rightEdges.getOrElse(from, Map[Node, Int]()).updated(to, position))
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

    // LEFT shortest path helpers
    def setShortestLeft(from: Node, to: Node, position: Int, length: Int): Unit = {
      shortestLeftPaths.getOrElseUpdate(from, mutable.HashMap.empty)
        .getOrElseUpdate(to, mutable.HashMap.empty)
        .getOrElseUpdate(position, length)
    }

    private def getShortestLeft(from: Node, to: Node, position: Int): Int = {
      shortestLeftPaths
        .getOrElse(from, mutable.Map[Node, mutable.Map[Int, Int]]())
        .getOrElse(to, mutable.Map[Int, Int]())
        .getOrElse(position, INFINITY)
    }

    // CFG shortest path rules
    /**
      * apply rule LEQ = LEQ LEQ
      *
      * @param from node of the new edge
      * @param mid node connecting the two existing edges
      * @param to node edging the new edge
      */
    private def ruleLeqLeq(from: Node, mid: Node, to: Node): Unit = {
      if (from entityInformationEquality to)
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

    def ruleLeftLeq(from: Node, mid: Node, to: Node, position: Int): Unit = {
      if (from entityInformationEquality to)
        return
      val leftDistance = getShortestLeft(from, mid, position)
      val rightDistance = getShortestLeq(mid, to)
      val currentDistance = getShortestLeft(from, to, position)

      if (leftDistance == INFINITY || rightDistance == INFINITY)
        return
      if (leftDistance + rightDistance < currentDistance) {
        setShortestLeft(from, to, position, leftDistance + rightDistance)
        inferLeftEdge(from, to, leftDistance + rightDistance, List(new Evidence(from, mid), new Evidence(mid, to)), atomic = false, position=position)
      }
    }

    def hasRightEdge(from: Node, to: Node, position: Int): Boolean = {
      if (rightEdges.contains(from))
        rightEdges(from).getOrElse(to, -1) == position
      else
        false
    }

    def ruleLeftRight(from: Node, mid: Node, to: Node, position: Int): Unit = {
      if (from entityInformationEquality to)
        return

      val leftDistance = getShortestLeft(from, mid, position)
      val currentDistance = getShortestLeq(from, to)

      if (leftDistance == INFINITY)
        return
      if (leftDistance + 1 < currentDistance) {
        setShortestLeq(from, to, leftDistance + 1)
        inferLeqEdge(from, to, leftDistance + 1, List(new Evidence(from, mid), new Evidence(mid, to)), atomic = false)
      }

    }

    def compatibleConstructors(constructorFrom: Node, constructorTo: Node): Boolean =
      constructorFrom.compatibleConstuctors(constructorTo)


    // TODO change this to use elements
    def expandNode(original: Node, subst: Node, equal: LessEqual) = {
//      if (constructorNodes.contains(original) && original.color == Black && subst.color == Black) {
//        constructorNodes(original).foreach(constructorNode => if (constructorNode.color == Black || !trace(constructorNode).contains(equal)) {
//          assert(constructorNode.isInstanceOf[Nodes.TypeNode])
//          assert(original.isInstanceOf[Nodes.TypeNode])
//          assert(subst.isInstanceOf[Nodes.TypeNode])
//          val replaced: List[Node] = replace(constructorNode.asInstanceOf[Nodes.TypeNode].tpe,
//            original.asInstanceOf[Nodes.TypeNode], subst.asInstanceOf[Nodes.TypeNode].tpe)
//          replaced.foreach(newNode => if (!graph.containsColorAgnostic(newNode)) {
//            graph = graph union Graph.apply(newNode)
//            if (constructorNode.color == White)
//              trace = trace.updated(newNode, trace(constructorNode) + equal)
//            else
//              trace = trace.updated(newNode, Set.empty + equal)
//
//            // change this to use elements
//            initTablesFor()
//          })
//        })
//      }
    }

    def addMoreEdges(edge: LessEqual): Unit = {
      val from = edge.from
      val to = edge.to

      if (constructorNodes.contains(from) || constructorNodes.contains(to)) {

        expandNode(from, to, edge)
        expandNode(to, from, edge)

        if (constructorNodes.contains(from) && constructorNodes.contains(to)) {
          for (constructorFrom <- constructorNodes(from)) {
            for (constructorTo <- constructorNodes(to)
            if compatibleConstructors(constructorFrom, constructorTo)
                 if !hasLeqEdge(from, to) || !hasLeqEdge(to, from)) {
              // by tests we know that the node has to be type node
              val fromChildren = graph.nodeEdgesMap(from).foldLeft(Seq[Edges.ConstructorEdge]()){
                (collector, edge) => edge match {
                  case e: Edges.ConstructorEdge if e.direction == Edges.ConstructorEdgeDirection.Decompositional => collector :+ e
                  case _ => collector
                }
              }.sortBy(edge => edge.position).map(_.to)
              val toChildren = graph.nodeEdgesMap(to).foldLeft(Seq[Edges.ConstructorEdge]()){
                (collector, edge) => edge match {
                  case e: Edges.ConstructorEdge if e.direction == Edges.ConstructorEdgeDirection.Decompositional => collector :+ e
                  case _ => collector
                }
              }.sortBy(edge => edge.position).map(_.to)

              if (fromChildren.zip(toChildren).forall(pair => hasLeqEdge(pair._1, pair._2))) {
                var size = 0
                var evidence: Seq[Evidence] = Seq.empty
                fromChildren.zip(toChildren).foreach{
                  pair =>
                    if (getShortestLeq(pair._1, pair._2) < INFINITY) {
                      size += getShortestLeq(pair._1, pair._2)
                      evidence = evidence :+ new Evidence(pair._1, pair._2)
                    } else
                      size += 1
                }
                inferLeqEdge(constructorFrom, constructorTo, size, evidence.toList, atomic = true)
              }
            }
          }
        }
      }
    }

    def saturation(): Unit = {
      val allNodes = graph.nodes

      //    var processedLengths = 0

      while (queue.nonEmpty) {
        val edge = queue.dequeue()

        // tryAddingExtraEdges, without constructors

//        edge match {
//          case a: LessEqual => addMoreEdges(a)
//          case _ => ()
//        }

        for (node <- allNodes) {
          edge match {
            case LessEqual(from, to, _) =>
              if (hasAtomicEdge(to, node))
                ruleLeqLeq(from, to, node)
              if (hasAtomicEdge(node, from))
                ruleLeqLeq(node, from, to)
            case LeftEdge(from, to, position, _) =>
              if (hasAtomicEdge(to, node))
                ruleLeftLeq(from, to, node, position)
              if (hasRightEdge(to, node, position))
                ruleLeftRight(from, to, node, position)
          }
        }
      }

    }

    override def hasLeqEdge(start: Node, end: Node): Boolean = getShortestLeq(start, end) != INFINITY
  }

}
