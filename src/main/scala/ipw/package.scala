import welder._
import inox._
import ipw.io.JsonIWFiles
import ipw.ast.ProofEvaluators

package object ipw {
  def assistedTheoryOf(pgm: InoxProgram) = new AssistedTheory with JsonIWFiles with ProofBuilder {
    override val program = pgm
  }
}