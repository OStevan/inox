package inox.parser.elaboration.type_graph

import inox.parser.elaboration.{Constraints, SimpleTypes}

import scala.collection.mutable

/**
  * Trait for giving path finding abilities.
  */
trait PathFinders {
  self: GraphStructure with Constraints with SimpleTypes with Elements =>

  /**
    * Class representing a path found by path finders.
    *
    * @param edges  constructing a path
    * @param finder used to generate the path
    */
  protected class GraphPath(val edges: Array[Edge], val finder: PathFinder) {
    assert(edges.length != 0, "Path should have at least one edge along its path ")

    /**
      * Increment the number of satisfiable paths passing through elements along the path.
      */
    def incrementSatisfiable(): Unit = {
      var edgeSet: Set[Edge] = Set.empty
      var nodeSet: Set[Node] = Set.empty

      firstInPath().incrementSatisfiable()

      nodeSet = nodeSet + firstInPath()

      for (k <- edges.indices) {
        if (!edgeSet.contains(edges(k))) {
          edges(k).incSatisfiableCount()
          edgeSet = edgeSet + edges(k)
        }
        if (!nodeSet.contains(edges(k).to)) {
          edges(k).to.incrementSatisfiable()
          nodeSet += edges(k).to
        }
      }
    }

    /**
      * Checks of from is less or equal to to structurally, without any prior knowledge
      *
      * @param from start node of the path
      * @param to   end node of the path
      * @return
      */
    private def leq(from: Node, to: Node): Boolean = {
      if (from entityInformationEquality to)
        return true

      if (from.isTrivialEnd || to.isTrivialEnd)
        return true

      to.accept(from)
    }

    def intersect(from: Node, to: Node): Color = from.element.intersect(to.element)

    /**
      * Method to get the first element in a path
      *
      * @return node representing the start of the path
      */
    def firstInPath(): Node = edges(0).from

    /**
      * Method to get the last element of the path
      *
      * @return nore representing the end node of the path
      */
    def lastInPath(): Node = edges(edges.length - 1).to

    /**
      * Checks if a path between two nodes is satisfiable
      *
      * @param from start node of the path
      * @param to   end node of the path
      * @return if the path is satisfiable
      */
    private def satisfiable(from: Node, to: Node): Boolean = {
      if (from entityInformationEquality to)
        return true

      if (leq(from, to))
        return true


      intersect(from, to)
    }

    /**
      * Checks if the path is satisfiable.
      *
      * @return path satisfiable flag
      */
    def isSatisfiablePath: Boolean = {
      if (edges.length == 0)
        return false
      satisfiable(firstInPath(), lastInPath())
    }

    /**
      * Checks if a relation is derivable
      *
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
      * Checks if the path is unsatisfiable
      *
      * @return
      */
    def isUnsatisfiable: Boolean = {
      if (edges.length == 0)
        return false

      !isSatisfiablePath
    }

    /**
      * Checks if the edge is informative based on the explanation from the paper
      *
      * @return
      */
    def isInformative: Boolean = {

      if (edges.length == 0)
        return false

      // trivially satisfiable not informative
      if (firstInPath().isTrivialEnd || lastInPath().isTrivialEnd)

      // path is trivially satisfiable
        if (firstInPath() entityInformationEquality lastInPath())
          return false

      // compatible types
      if (lastInPath() accept firstInPath())
        return false


      // add a check if an node is added during graph saturation if it is then a path is not informative

      val leqElements: mutable.Stack[Node] = mutable.Stack()
      val constructorConditions: mutable.Stack[(Int, Edges.ConstructorEdgeDirection.Direction)] = mutable.Stack()
      val firstNode = firstInPath()
      leqElements.push(firstNode)

      for (edge <- edges) {
        var shouldCompare = !edge.to.isTrivialEnd

        edge match {
          case Edges.ConstructorEdge(_, _, dir, pos) =>
            if (constructorConditions.isEmpty || !(constructorConditions.top._1 == pos && constructorConditions.top._2 != dir)) {
              constructorConditions.push((pos, dir))
              leqElements.push(edge.to)
              shouldCompare = false
            } else {
              constructorConditions.pop()
              leqElements.pop()
            }
          case _ => ()
        }

        if (shouldCompare) {
          // there are still non processed nodes
          if (leqElements.nonEmpty &&
            // path until here is not satisfiable
            !satisfiable(leqElements.top, edge.to) &&
            // we have reached the same element from were we started
            // edge from is the same as edge to
            !(leqElements.top entityInformationEquality firstInPath()) && (edge.to entityInformationEquality lastInPath()))
            return false
          else if (!edge.to.hasVars) {
            leqElements.pop()
            leqElements.push(edge.to)
          }
        }
      }
      // passes the check
      true
    }


    def pathNodes(): Seq[Node] = {
      var nodes: Set[Node] = Set.empty
      for (edge <- edges) {
        nodes = nodes + edge.from
        nodes = nodes + edge.to
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
      *
      * @param from   node
      * @param to     node
      * @param length of edge
      */
    protected case class LessEqual(from: Node, to: Node, length: Int) extends ReductionEdge

    /**
      * LEFT := original
      * LEFT := LEFT LEQ (position is inherited from the child LEFT)
      *
      * @param from     node
      * @param to       node
      * @param position position in constructor
      * @param length   of the edge
      */
    protected case class LeftEdge(from: Node, to: Node, position: Int, length: Int) extends ReductionEdge

    /**
      * Right edges are always of length 1 and are not represented with a class.
      */


    /**
      * Model a reverse edge connecting type class with a type
      *
      * @param from node of an edge
      * @param to   node of the edge
      */
    protected case class ReverseEdge(from: Node, to: Node) extends ReductionEdge {
      assert(from.element.isInstanceOf[TypeClassElement])
    }

    /**
      * Original edges are not represented with specific classes for the same reason as Right edges.
      * Intersection edges are only used as an end result so they are not stored in intermediate steps.
      */


    def getPath(from: Node, to: Node): List[Edge]

    def hasLeqEdge(from: Node, to: Node): Boolean

    def hasIntersectionEdge(from: Node, to: Node): Boolean
  }

  /**
    * Finds context free language reachable paths
    */
  abstract class CFLPathFinder extends PathFinder {

    protected var nodeEdgesMap: Map[Node, Set[Edge]] = _

    protected class Evidence(val from: Node, val to: Node)

    var graph: Graph = _

    protected val nextHop: mutable.Map[Node, mutable.Map[Node, List[Evidence]]] = mutable.Map()
    private val atomicEdges: mutable.Map[Node, mutable.Set[Node]] = mutable.Map()


    // public
    def this(graph: Graph) = {
      this()
      this.graph = graph
    }

    override def getPath(from: Node, to: Node): List[Edge] = {
      getLeqPath(from, to)
    }

    def inferLeqEdge(from: Node, to: Node, length: Int, evidence: List[Evidence], atomic: Boolean)

    // protected
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
      atomicEdges.getOrElseUpdate(from, new mutable.HashSet[Node]()).add(to)
    }

    protected def hasAtomicEdge(from: Node, to: Node): Boolean = {
      atomicEdges.getOrElseUpdate(from, new mutable.HashSet[Node]()).contains(to)
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
      val edges = nodeEdgesMap.getOrElse(from, Set())
      for (edge <- edges)
        if (edge.to == to)
          return edge

      // hack for intersection edges
      if (from.element.isInstanceOf[TypeClassElement]) {
        for (edge <- graph.nodeEdgesMap.getOrElse(to, Set.empty)) {
          if (edge.to == from)
            return ReverseEdge(from, to)
        }
      }
      null
    }

    protected def hasRightEdge(from: Node, to: Node, position: Int): Boolean

    protected def hasOriginalEdge(from: Node, to: Node): Boolean

    protected def hasReverseEdge(from: Node, to: Node): Boolean

    // CFG rules to be implemented by concrete path finders

    /**
      * apply rule LEQ = LEQ LEQ
      *
      * @param from node of the new edge
      * @param mid  node connecting the two existing edges
      * @param to   node edging the new edge
      */
    protected def ruleLeqLeq(from: Node, mid: Node, to: Node): Unit

    /**
      * apply rule LEFT = LEFT LEQ
      *
      * @param from     node of the new edge
      * @param mid      node connecting the two existing edges
      * @param to       node ending the new edge
      * @param position position in the constructor of the LEFT edge from the right-hand side
      */
    protected def ruleLeftLeq(from: Node, mid: Node, to: Node, position: Int): Unit

    /**
      * apply rule REV = REV LEQ
      *
      * @param from node starting the new edge
      * @param mid  node connecting the two existing edges
      * @param to   node ending the new edge
      */
    protected def ruleReverseLeq(from: Node, mid: Node, to: Node): Unit

    /**
      * apply rule LEQ = LEFT RIGHT
      *
      * @param from     node staring the new edge
      * @param mid      node connecting the two edges
      * @param to       node ending the new path
      * @param position inside the constructor on which two edges need to agree
      */
    protected def ruleLeftRight(from: Node, mid: Node, to: Node, position: Int): Unit

    /**
      * apply rule INTERSECT = REVERSE ORIGINAL
      *
      * @param from node starting the new edge
      * @param mid  node connecting the two edges
      * @param to   node ending the new edge
      */
    protected def ruleReverseOriginal(from: Node, mid: Node, to: Node): Unit
  }


  /**
    * Finds shortest paths
    */
  class ShortestPathFinder(g: Graph) extends CFLPathFinder(g) {
    private val INFINITY = Int.MaxValue
    private val shortestLEQPaths = new mutable.HashMap[Node, mutable.Map[Node, Int]]()
    private val shortestReversePaths = new mutable.HashMap[Node, mutable.Map[Node, Int]]()
    private val shortestIntersectPaths = new mutable.HashMap[Node, mutable.Map[Node, Int]]()
    private val shortestLeftPaths = new mutable.HashMap[Node, mutable.Map[Node, mutable.Map[Int, Int]]]()
    private var rightEdges: Map[Node, Map[Node, Int]] = Map.empty
    private var originalEdges: Map[Node, Set[Node]] = Map.empty

    // used for type class expanding
    private var expandedTypes: Set[(TypeElement, TypeClassElement)] = Set.empty
    private var expandedClasses: Set[(TypeClassElement, TypeClassElement)] = Set.empty

    // queue representing the context free reachability frontier
    val queue: mutable.Queue[ReductionEdge] = mutable.Queue[ReductionEdge]()



    init(graph)
    saturation()


    def init(g: Graph): Unit = {
      g.edges.foreach { edge =>
        if (nodeEdgesMap == null)
          nodeEdgesMap = g.nodeEdgesMap

        nodeEdgesMap = nodeEdgesMap.updated(edge.from, nodeEdgesMap.getOrElse(edge.from, Set.empty) + edge)

        edge match {
          case a: Edges.LessEqualEdge =>
            inferLeqEdge(a.from, a.to, 1, List.empty, atomic = true)
            if (a.to.element.isInstanceOf[TypeClassElement]) {
              inferReverse(a.to, a.from, 1, List.empty, atomic = true)
              insertOriginal(a.from, a.to)
            }
          case Edges.ConstructorEdge(from, to, Edges.ConstructorEdgeDirection.Original, position) =>
            inferLeftEdge(from, to, 1, List.empty, position, atomic = true)
          case Edges.ConstructorEdge(from, to, Edges.ConstructorEdgeDirection.Decompositional, position) =>
            insertRightEdge(from, to, position)
        }
      }
    }

    override def hasRightEdge(from: Node, to: Node, position: Int): Boolean = {
      if (rightEdges.contains(from))
        rightEdges(from).getOrElse(to, -1) == position
      else
        false
    }

    override def hasOriginalEdge(from: Node, to: Node): Boolean = {
      if (originalEdges.contains(from))
        originalEdges(from).contains(to)
      else
        false
    }


    override def hasReverseEdge(from: Node, to: Node): Boolean = getShortestReverse(from, to) != INFINITY


    // new edge inference either from constructed graph of using
    override def inferLeqEdge(from: Node, to: Node, length: Int, evidence: List[Evidence], atomic: Boolean): Unit = {
      if (from entityInformationEquality to)
        return
      addNextHop(from, to, evidence)
      queue.enqueue(LessEqual(from, to, length))
      setShortestLeqLength(from, to, length)
      if (atomic)
        addAtomicLeqEdge(from, to)
    }

    protected def inferLeftEdge(from: Node, to: Node, length: Int, evidence: List[Evidence], position: Int, atomic: Boolean): Unit = {
      if (from entityInformationEquality to)
        return
      addNextHop(from, to, evidence)
      queue.enqueue(LeftEdge(from, to, position, length))
      setShortestLeftLength(from, to, position, length)
    }

    protected def inferReverse(from: Node, to: Node, length: Int, evidence: List[Evidence], atomic: Boolean): Unit = {
      if (from entityInformationEquality to)
        return
      addNextHop(from, to, evidence)
      queue.enqueue(ReverseEdge(from, to))
      setShortestReverse(from, to, length)
    }


    protected def inferIntersectEdge(from: Node, to: Node, length: Int, evidence: List[ShortestPathFinder.this.Evidence]): Unit = {
      if (to entityInformationEquality from)
        return
      addNextHop(from, to, evidence)
      setShortestIntersect(from, to, length)
      expandOnIntersect(from, to)
    }


    // keep information about simple edges
    def insertRightEdge(from: Node, to: Node, position: Int): Unit = {
      rightEdges = rightEdges.updated(from, rightEdges.getOrElse(from, Map[Node, Int]()).updated(to, position))
    }

    def insertOriginal(from: Node, to: Node): Unit = {
      originalEdges = originalEdges.updated(from, originalEdges.getOrElse(from, Set[Node]()) + to)
    }

    // LEQ shortest path helpers
    private def getShortestLeqLength(start: Node, end: Node): Int =
      shortestLEQPaths.getOrElse(start, mutable.Map[Node, Int]()).getOrElse(end, INFINITY)


    private def setShortestLeqLength(start: Node, end: Node, length: Int): Unit =
      shortestLEQPaths.getOrElseUpdate(start, mutable.Map[Node, Int]()).update(end, length)

    // LEFT shortest path helpers
    def setShortestLeftLength(from: Node, to: Node, position: Int, length: Int): Unit = {
      shortestLeftPaths.getOrElseUpdate(from, mutable.HashMap.empty)
        .getOrElseUpdate(to, mutable.HashMap.empty)
        .getOrElseUpdate(position, length)
    }

    private def getShortestLeftLength(from: Node, to: Node, position: Int): Int = {
      shortestLeftPaths
        .getOrElse(from, mutable.Map[Node, mutable.Map[Int, Int]]())
        .getOrElse(to, mutable.Map[Int, Int]())
        .getOrElse(position, INFINITY)
    }

    // REVERSE shortest path helpers
    def setShortestReverse(from: Node, to: Node, length: Int): Unit = {
      assert(from.element.isInstanceOf[TypeClassElement])
      shortestReversePaths.getOrElseUpdate(from, mutable.Map[Node, Int]()).update(to, length)
    }

    def getShortestReverse(from: Node, to: Node): Int =
      shortestReversePaths.getOrElse(from, mutable.Map[Node, Int]()).getOrElse(to, INFINITY)

    // INTERSECT shortest path helpers
    def setShortestIntersect(from: Node, to: Node, length: Int): Unit = {
      shortestLEQPaths.getOrElseUpdate(from, mutable.Map[Node, Int]()).update(to, length)
    }

    def getShortestIntersect(from: Node, to: Node): Int = {
      shortestIntersectPaths.getOrElse(from, mutable.Map[Node, Int]()).getOrElse(to, INFINITY)
    }

    // CFG shortest path rules implementation
    override protected def ruleLeqLeq(from: Node, mid: Node, to: Node): Unit = {
      if (from entityInformationEquality to)
        return
      val leftDistance = getShortestLeqLength(from, mid)
      val rightDistance = getShortestLeqLength(mid, to)
      val currentDistance = getShortestLeqLength(from, to)

      if (leftDistance == INFINITY || rightDistance == INFINITY)
        return
      if (leftDistance + rightDistance < currentDistance) {
        setShortestLeqLength(from, to, leftDistance + rightDistance)
        inferLeqEdge(from, to, leftDistance + rightDistance, List(new Evidence(from, mid), new Evidence(mid, to)), atomic = false)
      }

    }

    override protected def ruleLeftLeq(from: Node, mid: Node, to: Node, position: Int): Unit = {
      if (from entityInformationEquality to)
        return
      val leftDistance = getShortestLeftLength(from, mid, position)
      val rightDistance = getShortestLeqLength(mid, to)
      val currentDistance = getShortestLeftLength(from, to, position)

      if (leftDistance == INFINITY || rightDistance == INFINITY)
        return
      if (leftDistance + rightDistance < currentDistance) {
        setShortestLeftLength(from, to, position, leftDistance + rightDistance)
        inferLeftEdge(from, to, leftDistance + rightDistance, List(new Evidence(from, mid), new Evidence(mid, to)), atomic = false, position = position)
      }
    }

    override protected def ruleReverseLeq(from: Node, mid: Node, to: Node): Unit = {
      if (from entityInformationEquality to)
        return
      val leftDistance = getShortestReverse(from, mid)
      val rightDistance = getShortestLeqLength(mid, to)
      val currentDistance = getShortestReverse(from, to)

      if (leftDistance == INFINITY || rightDistance == INFINITY)
        return
      if (leftDistance + rightDistance < currentDistance) {
        setShortestReverse(from, to, leftDistance + rightDistance)
        inferReverse(from, to, leftDistance + rightDistance, List(new Evidence(from, mid), new Evidence(mid, to)), atomic = false)
      }
    }


    override protected def ruleLeftRight(from: Node, mid: Node, to: Node, position: Int): Unit = {
      if (from entityInformationEquality to)
        return

      val leftDistance = getShortestLeftLength(from, mid, position)
      val currentDistance = getShortestLeqLength(from, to)

      if (leftDistance == INFINITY)
        return
      if (leftDistance + 1 < currentDistance) {
        setShortestLeqLength(from, to, leftDistance + 1)
        inferLeqEdge(from, to, leftDistance + 1, List(new Evidence(from, mid), new Evidence(mid, to)), atomic = false)
      }
    }


    override protected def ruleReverseOriginal(from: Node, mid: Node, to: Node): Unit = {
      if (from entityInformationEquality to)
        return
      val reverseDistance = getShortestReverse(from, mid)
      val currentDistance = getShortestIntersect(from, to)

      if (reverseDistance == INFINITY)
        return

      if (reverseDistance + 1 < currentDistance) {
        setShortestIntersect(from, to, reverseDistance + 1)
        inferIntersectEdge(from, to, reverseDistance + 1, List(new Evidence(from, mid), new Evidence(mid, to)))
      }
    }

    override def hasIntersectionEdge(from: Node, to: Node): Boolean = {
      getShortestIntersect(from, to) != INFINITY
    }


    private def addConstraints(constraints: Seq[Constraint]): Unit = {
      val g = constructSeq(constraints)
      init(g)
    }

    private def expandOnLEQ(equal: Edge): Unit = {
      if (equal.from == equal.to)
        return
      (equal.from.element, equal.to.element) match {
        case (first: TypeElement, second: TypeClassElement) if !expandedTypes.contains((first, second)) =>
          expandedTypes = expandedTypes + ((first, second))
          second.typeClass.accepts(first.tpe).foreach(constraints => addConstraints(constraints))

        case _ => ()
      }
    }

    def expandOnIntersect(from: Node, to: Node): Unit = {
      if (from == to)
        return
      (from.element, to.element) match {
        case (first: TypeClassElement, second: TypeClassElement)
          if !(expandedClasses.contains((first, second)) || expandedClasses.contains((second, first))) =>
          expandedClasses = expandedClasses + ((first, second))
          first.typeClass.combine(second.typeClass)(SimpleTypes.Unknown.fresh).foreach(constraints => addConstraints(constraints))
        case (_: TypeClassElement, _: TypeClassElement) => ()
        case _ =>
          assert(assertion = false, "Should never happen")
      }
    }

    def saturation(): Unit = {
      val allNodes = graph.nodes

      //    var processedLengths = 0

      while (queue.nonEmpty) {
        val edge = queue.dequeue()

        // tryAddingExtraEdges, without constructors
        edge match {
          case a: LessEqual => expandOnLEQ(a)
          case _ => ()
        }

        for (node <- allNodes) {
          edge match {
            case LessEqual(from, to, _) =>
              if (hasAtomicEdge(to, node))
                ruleLeqLeq(from, to, node)
              if (hasAtomicEdge(node, from))
                ruleLeqLeq(node, from, to)
              if (hasReverseEdge(node, from))
                ruleReverseLeq(node, from, to)
            case LeftEdge(from, to, position, _) =>
              if (hasAtomicEdge(to, node))
                ruleLeftLeq(from, to, node, position)
              if (hasRightEdge(to, node, position))
                ruleLeftRight(from, to, node, position)
            case ReverseEdge(from, to) =>
              if (hasOriginalEdge(to, node))
                ruleReverseOriginal(from, to, node)
              if (hasLeqEdge(to, node))
                ruleReverseLeq(from, to, node)
          }
        }
      }

    }

    override def hasLeqEdge(start: Node, end: Node): Boolean = getShortestLeqLength(start, end) != INFINITY
  }

}
