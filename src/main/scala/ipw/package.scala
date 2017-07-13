import welder._
import inox._
import ipw.io.JsonIWFiles

package object ipw {
  def assistedTheoryOf(pgm: InoxProgram): AssistedTheory = new AssistedTheory with JsonIWFiles with TheoremBuilder {
    override val program = pgm
  }
}