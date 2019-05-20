package inox.parser.elaboration.type_graph

class RankingMetric (val C1: Double, val C2: Double) {
  def getScore(setSize: Double, successCount: Double): Double = {
    C1 * setSize + successCount * C2
  }
}

object RankingMetric {

  val default = new RankingMetric(3, 1)
}
