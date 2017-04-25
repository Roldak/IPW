import welder._

package object ipw {
  def assistantOf(thry: Theory): Assistant = new Assistant {
    override val theory = thry
  }
}