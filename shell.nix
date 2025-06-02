{
  mkShellNoCC,
  typst,
  git,
}:
mkShellNoCC {
  name = "Probability and Statistics - Cheat Sheet";
  DIRENV_LOG_FORMAT = "";
  packages = [typst git];
}
