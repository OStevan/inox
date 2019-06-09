package inox.parser.elaboration.type_graph


import scala.collection.mutable

trait ErrorReasonSearch { self: PathFinders with ErrorReasons =>

  /**
    * Abstract class encapsulation the A* search algorithm to find the most likely error source
    * @param candidates which might be the most likely source of an error
    * @param paths which are unsatisfiable in the type graph
    * @param suboptimal number of suboptimal results we would also like to output, interesting to see how the algorithm works
    */
  abstract class HeuristicSearchAlgorithm (val candidates: Array[Entity], val paths: List[GraphPath], val suboptimal: Int) {

    // current best cost for error
    private var best = Double.MaxValue
    // how many suboptimal suggestions we are interested in
    private var suboptimalCount = 0

    /**
      * One A* search node encapsulating the current search state
      * @param entities inside this node
      * @param candidate entity for this node
      * @param index index in the array of the candidates
      * @param remaining unsatisfiable paths to process
      * @param estimation cost for this node
      */
    protected class SearchNode(val entities: Set[Entity], val candidate: Entity, val index: Int,
                               val remaining: Seq[GraphPath], val estimation: Double)

    /**
      * ordering to be used for a priority queue representing the search frontier
      */
    protected implicit val ordering: Ordering[SearchNode] = new Ordering[SearchNode] {
      override def compare(x: SearchNode, y: SearchNode): Int = -x.estimation.compare(y.estimation)
    }

    /**
      * Main search function which returns the set of the most likely error entities
      * @return likely error entities
      */
    def findOptimal(): Set[Reason] = {
      var result: Set[Reason] = Set.empty
      // search frontier, sorted by estimation of the cost
      val queue: mutable.PriorityQueue[SearchNode] = mutable.PriorityQueue[SearchNode]()

      for (i <- candidates.indices) {
        addSearchNode(queue, candidates(i), i, new SearchNode(Set.empty, candidates(0), 0, paths, 0))
      }

      while (queue.nonEmpty) {
        val node = queue.dequeue()

        val (flag, set) = goalTest(result, node)
        result = set

        // check if the goal is found
        if (flag)
          return result

        for (i <- node.index until candidates.length - 1) {
          addSearchNode(queue, candidates(i + 1), i + 1, node)
        }
      }

      result
    }

    /**
      * Check if a goal is reached and return the set of entities which represent this goal
      * @param set of reasons why the graph is inconsistent
      * @param node search node which is checked as goal
      * @return pair, goal found and current reason set
      */
    private def goalTest(set: Set[Reason], node: SearchNode): (Boolean, Set[Reason]) = {
      val estimate = node.estimation

      // all paths need to be processed
      if (node.remaining.nonEmpty)
        (false, set)
      else {

        // update current best value with the estimate for the first node
        if (best == Double.MaxValue)
          best = estimate


        if (estimate <= best || suboptimalCount <= suboptimal) {
          if (estimate > best)
            suboptimalCount += 1
          if (estimate < best) {
            best = estimate
            (false, Set(Reason(node.entities, estimate)))
          } else {
            (false, set + Reason(node.entities, estimate))
          }
        } else
          (true, set)
      }
    }

    /**
      * Adds a new search node by adding a new entity to the ones from the previous search node
      * @param frontier current search frontier of the A* algorithm
      * @param candidate most likely error source entity to be added
      * @param candidateIndex index of the candidate
      * @param previousNode in the search space
      * @return updated search frontier
      */
    protected def addSearchNode(frontier: mutable.PriorityQueue[SearchNode], candidate: Entity,
                                candidateIndex: Int, previousNode: SearchNode): mutable.PriorityQueue[SearchNode]
  }

  class ExplanationFinder (candidates: Array[Entity], paths: List[GraphPath], suboptimal: Int)
    extends HeuristicSearchAlgorithm(candidates, paths, suboptimal) {
    private var metric = RankingMetric.default
    // map to store for each entity how many paths depend on the entity
    var dependency: Map[Entity, Set[GraphPath]] = Map()
    var duplicateExists = false
    var increment = 1


    def this(candidates: Array[Entity], paths: List[GraphPath], suboptimal: Int, C1: Double, C2: Double) = {
      this(candidates, paths, suboptimal)
      this.metric = new RankingMetric(C1, C2)
    }

    {
      var can: Set[Entity] = Set()
      for (entity <- candidates) {
        dependency = dependency.updated(entity, mapsTo(entity))
        if (!candidates.contains(entity))
          can = can.+(entity)
      }
    }

    /**
      * Estimates the heuristic factor based on the entity and the remaining paths
      * @param paths to satisfy
      * @param index of the candidate
      * @return value of the estimate
      */
    def heuristicFactor(paths: Seq[GraphPath], index: Int): Double = {
      if (paths.isEmpty)
        return 0

      for (i <- index until candidates.length;
           entity = candidates(i)

           if dependency(entity).size < paths.size) {

        val isCut = paths.forall(path => dependency(entity).contains(path))

        // case when only one entity covers all remaining paths
        if (isCut)
          return increment
      }
      // case when it is covered by multiple entities
      2 * increment
    }

    /**
      * Adds one search node to the frontier
      * @param frontier of the search state
      * @param candidate most likely error source entity to be added
      * @param candidateIndex index of the candidate
      * @param previous search node
      * @return updated search frontier
      */
    override protected def addSearchNode(frontier: mutable.PriorityQueue[SearchNode],
                                         candidate: Entity, candidateIndex: Int, previous: SearchNode): mutable.PriorityQueue[SearchNode]= {
      var remaining: Set[GraphPath] = Set.empty
      val toSatisfy: Set[GraphPath] = previous.remaining.toSet
      val entities: Set[Entity] = previous.entities + candidate

      // paths to satisfy after this entity is added
      for (path <- toSatisfy) {
        if (!dependency(candidate).contains(path))
          remaining = remaining + path
      }

      var satisfiableCount: Double = 0
      // number of satisfiable paths which go through this entity
      for (entity <- entities)
        satisfiableCount += entity.satisfiablePathsCount

      var candidatesSet: Set[Entity] = Set.empty
      var size: Double = 0
      for (entity <- entities) {
        if (candidatesSet.contains(entity)) {
          // check what to do with duplicates
          size += increment
        } else {
          candidatesSet = candidatesSet + entity
          size += 1
        }
      }

      val realCost = metric.getScore(size, satisfiableCount)
      val heuristicEstimate = metric.getScore(heuristicFactor(remaining.toSeq, candidateIndex + 1), 0)

      val newNode = new SearchNode(entities, candidate, candidateIndex, remaining.toSeq, realCost + heuristicEstimate)

      frontier.enqueue(newNode)
      frontier
    }


    /**
      * Collects all paths which can be explained by one entity, in the current implementation it only depends on positions
      * @param entity for which we want to get paths
      * @return set of paths
      */
    private def mapsTo(entity: Entity): Set[GraphPath] = {
      var ret: Set[GraphPath] = Set.empty
      for (path <- paths) {
        if (entity.explainsPath(path))
          ret = ret + path
      }
      ret
    }
  }
}
