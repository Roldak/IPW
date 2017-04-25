import welder._
import inox._

package object ipw {
  def assistedTheoryOf(pgm: InoxProgram): AssistedTheory = new AssistedTheory {
    override val program = pgm
  }
}