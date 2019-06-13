package inox.parser.elaboration.type_graph

import inox.parser.elaboration.{Constraints, SimpleTypes}

import scala.util.parsing.input.{NoPosition, Position}

trait GraphStructure {
  self: Elements with SimpleTypes with Constraints =>

  import Edges._
  import Constraints._

  type Color = Boolean
  val WHITE: Color = true
  val BLACK: Color = false

  object ElemNodeMap {
    private var elemNodeMap: Map[Element, Node] = Map.empty

    def getNode(elem: Element, color: Color): Node = {
      if (elemNodeMap.contains(elem))
        elemNodeMap(elem)
      else {
        val node = Node(elem, color)
        elemNodeMap = elemNodeMap.updated(elem, node)
        node
      }
    }
  }

  case class Node(element: Element, color: Color) {
    def isWhite(): Boolean = color == WHITE


    def isConstructor: Boolean = element.isConstructor

    def compatibleConstructors(constructorTo: Node): Boolean = element.compatibleConstructors(constructorTo.element)

    private var counter: Int = 0

    /**
      * Test if the information inside the nodes is the same, basically type equality of typeclass equality
      *
      * @param other node with which to compare
      * @return
      */
    def entityInformationEquality(other: Node): Boolean = element.informationEquality(other.element)

    def incrementSatisfiable(): Unit = counter = counter + 1

    def satisfiableCount(): Int = counter

    def hasVars: Boolean = element.hasVars

    def isTrivialEnd: Boolean = element.isTrivialEnd

    /**
      * Checks if this node can accept other node, basically used for type classes
      *
      * @param other node to accept
      * @return flag if this Node accepts the other
      */
    def accept(other: Node): Boolean = element.accept(other.element)

    def combine(node: Node): Boolean = element.combine(node.element)

    def pos: Position = element.position

    override def equals(obj: Any): Boolean = obj match {
      case Node(ent, _) => ent == this.element
      case _ => false
    }
  }

  trait Edge {
    private var counter = 0

    def incSatisfiableCount(): Unit = counter = counter + 1

    def satisfiableCount(): Int = counter

    def from: Node

    def to: Node
  }

  object Edges {

    object ConstructorEdgeDirection {

      trait Direction

      case object Original extends Direction

      case object Decompositional extends Direction

    }

    import ConstructorEdgeDirection._

    case class LessEqualEdge(from: Node, to: Node) extends Edge

    case class ConstructorEdge(from: Node, to: Node, direction: Direction, position: Int) extends Edge

  }

  case class Graph private(nodeEdgesMap: Map[Node, Set[Edge]], edges: Set[Edge], elementNodeMap: Map[Element, Node]) {
    def nodes: Set[Node] = nodeEdgesMap.keySet

    def this(nodes: Set[Node], edges: Set[Edge]) {
      this(Graph.makeNodeEdgesMap(nodes, edges), edges, Graph.maleElementNodeMap(nodes))
    }

    def union(other: Graph): Graph = new Graph(this.nodeEdgesMap.keySet union other.nodeEdgesMap.keySet, this.edges union other.edges)

    def addEdge(edge: Edge): Graph = {
      edge match {
        case LessEqualEdge(from, to) =>
          assert(nodeEdgesMap.keySet.contains(from) && nodeEdgesMap.keySet.contains(to))
          new Graph(nodeEdgesMap.updated(from, nodeEdgesMap.getOrElse(from, Set()) + edge), edges + edge, elementNodeMap)
        case ConstructorEdge(from, to, _, _) =>
          assert(nodeEdgesMap.keySet.contains(from) && nodeEdgesMap.keySet.contains(to))
          new Graph(nodeEdgesMap.updated(from, nodeEdgesMap.getOrElse(from, Set()) + edge), edges + edge, elementNodeMap)
      }
    }
  }

  object Graph {
    private def maleElementNodeMap(nodes: Set[Node]): Map[Element, Node] = nodes.map(elem => (elem.element, elem)).toMap

    private def makeNodeEdgesMap(nodes: Set[Node], edges: Set[Edge]): Map[Node, Set[Edge]] = {
      var nodeEdgesMap: Map[Node, Set[Edge]] = Map.empty

      nodes.foreach(node => nodeEdgesMap = nodeEdgesMap.updated(node, Set.empty))

      edges.foreach {
        case edge: LessEqualEdge => nodeEdgesMap = nodeEdgesMap.updated(edge.from, nodeEdgesMap.getOrElse(edge.from, Set()) + edge)
        case edge: ConstructorEdge => nodeEdgesMap = nodeEdgesMap.updated(edge.from, nodeEdgesMap.getOrElse(edge.from, Set()) + edge)
      }

      nodeEdgesMap
    }
  }

  def constructSeq(constraints: Seq[Constraint], color: Color): Graph = {
    val (nodes, edges) = constraints.map((constraint: Constraint) => construct(constraint, color)).foldLeft((Set.empty[Node], Set.empty[Edge])) {
      case (acc, graph) => (acc._1 union graph._1, acc._2 union graph._2)
    }

    new Graph(nodes, edges)
  }

  def construct(constraint: Constraint, color: Color): (Set[Node], Set[Edge]) = constraint match {
    case Equals(left, right) =>
      val (leftNode: Node, leftGraph) = construct(left, color)
      val (rightNode: Node, rightGraph) = construct(right, color)
      (
        leftGraph._1 union rightGraph._1,
        leftGraph._2 union rightGraph._2 union Set(
          LessEqualEdge(leftNode, rightNode),
          LessEqualEdge(rightNode, leftNode)
        ))
    case HasClass(elem, typeClass) =>
      val (elemNode, elemGraph) = construct(elem, color)
      val typeClassNode = ElemNodeMap.getNode(TypeClassElement(typeClass, constraint.pos), color)
      (
        elemGraph._1 + typeClassNode,
        elemGraph._2 + LessEqualEdge(elemNode, typeClassNode)
      )
    case _ =>
      // ignore exists currently
      (Set.empty, Set.empty)
  }

  def construct(tpe: SimpleTypes.Type, color: Color): (Node, (Set[Node], Set[Edge])) = {
    //    if ()
    //    if (tpe.pos == NoPosition)
    //      assert(tpe.pos == NoPosition, "Every type should have a position for graph analysis")
    tpe match {
      case SimpleTypes.FunctionType(froms, to) =>
        val (toNode, toGraph) = construct(to, color)
        val funNode = ElemNodeMap.getNode(TypeElement(tpe), color)

        val startGraph = (
          toGraph._1 + funNode, // node union
          toGraph._2 union Set( // edge union
            ConstructorEdge(toNode, funNode, ConstructorEdgeDirection.Original, froms.length),
            ConstructorEdge(funNode, toNode, ConstructorEdgeDirection.Decompositional, froms.length)
          ))

        (funNode,
          froms.foldLeft((0, startGraph))((pair, elem) => {
            val (elemNode, elemGraph) = construct(elem, color)
            (pair._1 + 1, (
              pair._2._1 union elemGraph._1, // node union
              pair._2._2 union elemGraph._2 union // edge union
                Set(ConstructorEdge(elemNode, funNode, ConstructorEdgeDirection.Original, pair._1),
                  ConstructorEdge(funNode, elemNode, ConstructorEdgeDirection.Decompositional, pair._1)))
            )

          })._2
        )
      case SimpleTypes.TupleType(elems) =>
        val tupleType = ElemNodeMap.getNode(TypeElement(tpe), color)

        (tupleType,
          elems.foldLeft((0, (Set(tupleType), Set.empty[Edge])))((pair, elem) => {
            val (elemNode, elemGraph) = construct(elem, color)
            (pair._1 + 1, (
              pair._2._1 union elemGraph._1,
              pair._2._2 union elemGraph._2 union Set(
                ConstructorEdge(elemNode, tupleType, ConstructorEdgeDirection.Original, pair._1),
                ConstructorEdge(tupleType, elemNode, ConstructorEdgeDirection.Decompositional, pair._1)))
            )
          })._2
        )
      case SimpleTypes.BagType(elemType) =>
        val bagNode = ElemNodeMap.getNode(TypeElement(tpe), color)
        val (elemNode, elemGraph) = construct(elemType, color)
        (bagNode, (
          elemGraph._1 + bagNode,
          elemGraph._2 union Set(
            ConstructorEdge(elemNode, bagNode, ConstructorEdgeDirection.Original, 0),
            ConstructorEdge(bagNode, elemNode, ConstructorEdgeDirection.Decompositional, 0)
          )
        ))
      case SimpleTypes.SetType(elemType) =>
        val setNode = ElemNodeMap.getNode(TypeElement(tpe), color)
        val (elemNode, elemGraph) = construct(elemType, color)
        (setNode, (
          elemGraph._1 + setNode,
          elemGraph._2 union Set(
            ConstructorEdge(elemNode, setNode, ConstructorEdgeDirection.Original, 0),
            ConstructorEdge(setNode, elemNode, ConstructorEdgeDirection.Decompositional, 0)
          )
        ))
      case SimpleTypes.ADTType(_, args) =>
        val adtNode = ElemNodeMap.getNode(TypeElement(tpe), color)
        (adtNode,
          args.foldLeft((0, (Set(adtNode), Set.empty[Edge])))((pair, elem) => {
            val (elemNode, elemGraph) = construct(elem, color)
            (pair._1 + 1, (
              pair._2._1 union elemGraph._1,
              pair._2._2 union elemGraph._2 union Set(
                ConstructorEdge(elemNode, adtNode, ConstructorEdgeDirection.Original, pair._1),
                ConstructorEdge(adtNode, elemNode, ConstructorEdgeDirection.Decompositional, pair._1)))
            )
          })._2
        )
      case SimpleTypes.MapType(from, to) =>
        val (fromNode, fromGraph) = construct(from, color)
        val (toNode, toGraph) = construct(to, color)
        val mapNode = ElemNodeMap.getNode(TypeElement(tpe), color)
        (mapNode,
          (fromGraph._1 union toGraph._1 + mapNode,
            fromGraph._2 union toGraph._2 union Set(
              ConstructorEdge(fromNode, mapNode, ConstructorEdgeDirection.Original, 0),
              ConstructorEdge(mapNode, fromNode, ConstructorEdgeDirection.Decompositional, 0),
              ConstructorEdge(toNode, mapNode, ConstructorEdgeDirection.Original, 1),
              ConstructorEdge(mapNode, toNode, ConstructorEdgeDirection.Decompositional, 1))
          )
        )
      case a: SimpleTypes.Type =>
        val node = ElemNodeMap.getNode(TypeElement(tpe), color)
        (node, (Set(node), Set.empty[Edge]))
    }
  }
}
