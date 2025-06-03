// CONFIGURATION
#set document(
  author: "Dominik Schwaiger",
  description: "Cheat Sheet for the Probability and Statistics Exam in FS25 at ETH",
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

#set text(size: 1em, lang: "en")
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

// VARIABLES

#let _block = block.with(inset: 4pt, radius: 2pt, width: 100%, breakable: true);
#let def(body) = _block(body, stroke: blue)
#let note(body) = _block(body, stroke: orange)
#let form(body) = _block(body, stroke: black)
#let not_relevant(body) = _block(body, stroke: (paint: gray, dash: "dashed"))

#underline()[= Probability and Statistics - Cheat Sheet]

#columns(2)[
  #def[Definitions, Lemmas, Propositions, etc.]
  #note[Notes, Examples]

  #colbreak()

  #form[Formulas]
  #not_relevant[Not Relevant]
]

== Probability space

#def[
  #columns(2)[
    $Omega$: *Sample Space*
    #colbreak()
    $omega in Omega$: *outcome*, elementary experiment
  ]

  #note(
    align(center)[
      Dice Throw: $Omega = {1,2,3,4,5,6}$
    ],
  )
]

=== Sigma Algebra

#def[
  #align(center)[$F$ *sigma algebra* $<=>$ $F subset P(Omega)$ and]
  + $Omega in F$
  + $A in F => A^C in F$
  + $A_1,A_2,... in F => union^infinity_{i=1}{A_i in F}$

  #note[
    #align(center)[$Omega={1,2,3,4,5,6}$]
    #columns(2)[
      $F={emptyset, {1,2,3,4,5,6}}$
      #colbreak()
      $F=P(Omega)$
    ]
  ]
]
