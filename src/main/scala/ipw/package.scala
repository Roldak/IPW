import welder._

package object ipw {
  def assistWith(thry: Theory): Assistant = new Assistant {
    override val theory = thry
  }
}