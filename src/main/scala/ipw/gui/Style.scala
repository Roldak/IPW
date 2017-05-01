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
    
    val previewStyle = """
      -fx-border-color: rgb(200, 100, 100);
      -fx-border-width: 2 0 2 0;
    """
    
    val goalStyle = """
      -fx-background-color: rgb(240, 240, 240);
      -fx-border-color: black;
      -fx-border-width: 1 0 1 0;
    """
  }
}