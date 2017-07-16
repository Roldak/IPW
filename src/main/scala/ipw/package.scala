import welder._
import inox._
import ipw.io.JsonIWFiles

package object ipw {
  def assistedTheoryOf(pgm: InoxProgram) = new AssistedTheory with JsonIWFiles with TheoremBuilder {
    override val program = pgm
  }
}