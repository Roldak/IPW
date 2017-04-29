package ipw.gui

trait Styles {
  object Style {
    val tfStyle = """
      -fx-background-color: rgb(250, 250, 250);
      -fx-border-color: black;
      -fx-border-size: 1px;
    """

    val eqStyle = """
      -fx-background-color: rgb(250, 250, 250);
      -fx-border-color: black;
      -fx-border-width: 0 0 1 0;
    """

    val eqHoverStyle = """
      -fx-background-color: rgb(255, 255, 255);
      -fx-border-color: rgb(30, 30, 90);
      -fx-border-width: 0 0 1 0;
    """
  }
}