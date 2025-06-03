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

#set text(size: 10pt, lang: "en")
#set par(spacing: 6pt)
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
      text(size: 7pt)[Source: #link("https://gitlab.dominik-schwaiger.ch/quio/Probability_and_Statistics-Cheat_Sheet")],
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

// BOXES

#let _block = block.with(inset: 6pt, radius: 2pt, width: 100%, breakable: true);
#let def(body) = _block(body, stroke: blue)
#let note(body) = _block(body, stroke: orange)
#let form(body) = _block(body, stroke: black)
#let not_relevant(body) = _block(body, stroke: (paint: gray, dash: "dashed"))

// HELPERS
#let spread = grid.with(
  columns: (auto, 1fr),
  align: (left, right),
)

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
  #columns(2)[
    + $Omega in F$
    + $A in F => A^C in F$
    #colbreak()
    3. $A_1,A_2,... in F => union^infinity_(i=1)A_i in F$
  ]

  #note[
    #align(center)[$Omega={1,2,3,4,5,6}$]
    #columns(2)[
      $F={emptyset, {1,2,3,4,5,6}}$
      #colbreak()
      $F=P(Omega)$
    ]
  ]
]

=== Probability measure

#def[
  #align(center)[$PP$ a *probability measure* on $(Omega, F)$ $<=>$ $PP$ a map:]
  $
    P: F &-> [0,1] \
    A &|-> PP[A]
  $
  #align(center)[and]
  + $PP[Omega] = 1$
  + (*countable additivity*) $PP[A] = sum^infinity_(i=1)PP[A_i] "if" A = union^infinity_(i=1)A_i$
  \
  #align(center)[$(Omega, F, PP)$ is a *probability space*]
]

=== Terminology

#def[
  #columns(2)[
    $A$ *occurs* $<=>$ $omega in A$
    #colbreak()
    $A$ *does not occur* $<=>$ $omega in.not A$
  ]

  #note[
    #columns(2)[
      $A in emptyset$ never occurs
      #colbreak()
      $A in Omega$ always occurs
    ]
  ]
]

=== Laplace model

#def[
  #align(center)[*Laplace model* on $Omega$ is a triple $(Omega, F, PP)$ where]
  #spread(
    [1. $F in P(Omega)$],
    [2. $PP: F -> [0,1], forall A in F: PP[A] = (|A|) / (|Omega|)$],
  )
]

=== Properties

#def[
  #columns(2)[
    + $emptyset in F$
    + $A_1, A_2, ..., in F => sect^infinity_(i=1)A_i in F$
    #colbreak()
    3. $A,B in F => A union B in F$
    + $A,B in F => A sect B in F$
  ]
  #line(length: 100%, stroke: gray)
  #columns(2)[
   5. $PP[emptyset] = 0$ 
   #colbreak()
   6. $PP[A^C] = 1 - PP[A]$
  ]
  7. $PP[A union B] = PP[A] + PP[B] - PP[A sect B]$
  + (*additivity*) $A_1,...,A_k$ _pairwise disjoint_, $PP[A_1 union ... union A_k]=PP[A_1] + ... + PP[A_k]$
  + (*Monotonicity*) $A subset B => PP[A] <= PP[B]$
  + (*Union bound*) $A_1, A_2, ...$ a sequence $=> PP[union^infinity_(i=1)A_i] <= sum^infinity_(i=1)PP[A_i]$
  + (*Increasing Limit*) $(A_n)$ increasing ($A_n subset A_(n+1)$) $=> lim_(n->infinity)PP[A_n]=PP[union^infinity_(n=1)A_n]$
  + (*Decreasing Limit*) $(B_n)$ decreasing ($B_n supset B_(n+1)$) $=> lim_(n->infinity)PP[B_n]=PP[sect^infinity_(n=1)B_n]$
]
