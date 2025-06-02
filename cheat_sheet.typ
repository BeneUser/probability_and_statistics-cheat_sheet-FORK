// CONFIGURATION
#set document(
  author: "Dominik Schwaiger",
  keywords: (
    "Spick",
    "Probability and Statistics",
    "Wahrscheinlichkeit und Statistik",
    "ETH",
    "Prüfung",
    "Exam",
    "Cheat Sheet",
  ),
  title: "Probability and Statistics - Cheat Sheet",
)

#set text(size: 12pt, lang: "en")
#set par(spacing: 0.5em)
#set page(
  flipped: true,
  numbering: "1/1",
  columns: 3,
  paper: "a4",
  margin: (rest: 0.25cm, bottom: 0.75cm),
  footer: context [
    #grid(
      columns: (1fr, 1fr, 1fr),
      align: (left, center, right),
      text(
        size: 0.5em,
      )[Source: #link("https://gitlab.dominik-schwaiger.ch/quio/Probability_and_Statistics-Cheat_Sheet")],
      [#counter(page).display(
          "1 of 1",
          both: true,
        )],
      [
        Revision: #raw(sys.inputs.at("REV", default: "local")), #datetime.today().display("[day].[month].[year repr:last_two]")
      ],
    )
  ],
)
#set columns(gutter: 12pt)
#set enum(numbering: "1a1.")
#set underline(offset: 1pt)

#underline()[= Probability and Statistics - Cheat Sheet]
