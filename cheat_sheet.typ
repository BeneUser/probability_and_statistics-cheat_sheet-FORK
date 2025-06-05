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
#set line(stroke: gray, length: 100%)

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

#columns(
  2,
  text(size: 0.5em)[
    #def[Definitions, Lemmas, Propositions, etc.]
    #note[Notes, Examples]

    #colbreak()

    #form[Formulas]
    #not_relevant[Not Relevant]
  ],
)

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
    + $A_1, A_2, ..., in F => inter^infinity_(i=1)A_i in F$
    #colbreak()
    3. $A,B in F => A union B in F$
    + $A,B in F => A inter B in F$
  ]
  #line()
  #columns(2)[
    5. $PP[emptyset] = 0$
    #colbreak()
    6. $PP[A^C] = 1 - PP[A]$
  ]
  7. $PP[A union B] = PP[A] + PP[B] - PP[A inter B]$
  + $A_1,...,A_k$ _pairwise disjoint_, $PP[A_1 union ... union A_k]=PP[A_1] + ... + PP[A_k]$ (*additivity*)
  + $A subset B => PP[A] <= PP[B]$ (*Monotonicity*)
  + $A_1, A_2, ...$ a sequence $=> PP[union^infinity_(i=1)A_i] <= sum^infinity_(i=1)PP[A_i]$ (*Union bound*)
  + $(A_n)$ increasing ($A_n subset A_(n+1)$) $=> lim_(n->infinity)PP[A_n]=PP[union^infinity_(n=1)A_n]$ (*Increasing Limit*)
  + $(B_n)$ decreasing ($B_n supset B_(n+1)$) $=> lim_(n->infinity)PP[B_n]=PP[inter^infinity_(n=1)B_n]$ (*Decreasing Limit*)
]

== Conditional probabilities

#def[
  #align(center)[
    conditional probability of *$A$ given $B$*
    $ PP[A | B] = (PP[A inter B]) / (PP[B]) $

  ]

  #note[$ PP[B|B] = 1 $]
]

=== Properties

#def[
  + $PP[.|B]$ is a *probability measure* on $Omega$
  #align(center)[$B_1, ..., B_n$ a *partition*#footnote([$Omega = B_1 union ... union B_n$ and pairwise disjoint]) of $Omega$ with $PP[B_i] > 0$]
  + $forall A in F: PP[A] = sum^n_(i=1)PP[A|B_i]PP[B_i]$ (*Formula of total probability*)
  + $PP[A>0] => PP[B_i | A ] = (PP[A|B_i]PP[B_i]) / (sum^n_(j=1)PP[A|B_j]PP[B_j])$ (*Bayes formula*)
]

== Independence

#def[
  #align(center)[$A$ and $B$ *independent* $<=> PP[A inter B] = PP[A]PP[B]$]

  #line()

  #align(center)[If $PP[A],PP[B] > 0$ then the following are equivalent:]
  #align(center)[+ $PP[A inter B] = PP[A]PP[B]$]
  #columns(2)[
    2. $PP[A | B]=PP[A]$
    #colbreak()
    3. $PP[B|A]=PP[B]$
  ]

  #line()
  #align(center)[$(A_i)_(i in I)$ *independent* $<=>$ $ forall J subset I "finite" space PP[inter_(j in J)A_j] = product_(j in J) $]

  #note[
    #align(center)[
      $A,B,C$ *independent* $<=>$
      #columns(2)[
        + $PP[A inter B] = PP[A]PP[B]$
        + $PP[A inter C] = PP[A]PP[C]$
        #colbreak()
        3. $PP[B inter C] = PP[B]PP[C]$
      ]
      4. $PP[A inter B inter C] = PP[A]PP[B]PP[C]$
    ]
  ]
]

== Random variables

#def[
  #align(center)[
    $X$ *random variable* $<=>$ $X$ a map $X: Omega -> RR$ and $forall a in RR: {omega in Omega: X(omega) <= a} in F$
  ]
]

=== Indicator Function

#def[
  #align(center)[
    *indicator function* $bb(1)_A$ of $A$:

    $ forall omega in Omega: bb(1)_A(omega) = cases(0 "if" omega in.not A, 1 "if" in A) $
  ]
]

== Distribution function

#def[
  #align(center)[
    *distribution function* of $X$: $ F_X: RR -> [0,1], space forall a in RR: F_X (a) = PP[X <= a] $
  ]
]

=== Properties

#def[
  #columns(2)[
    + $PP[a < X <= b] = F(b) - F(a)$
    + $F$ is non-decreasing
    #colbreak()
    3. $F$ is right continuous
    + $lim_(a -> - infinity) F(a) = 0$ and $lim_(a -> infinity) F(a) = 1$
  ]
]

=== Independence

#def[
  #align(center)[$X_1, ..., X_n$ *independent* $<=> forall x_1, ..., x_n in RR:$]
  $ PP[X_1 <= x_1, ..., X_n <= x_n] = PP[X_1 <= x_1] dots.c PP[X_n <= x_n] $
]

#not_relevant[
  (*grouping*) $X_1, ..., X_n$ independent, $1 <= i_1 < dots.c < i_k <= n$ indices, $phi.alt_1, ..., phi.alt_k$ functions, this is *independent*:
  $ Y_1 = phi.alt_1 (X_1, ..., X_(i_1)), ..., Y_k = phi.alt_k (X_(i_(k-1) + 1), ..., X_(i_k)) $
]

=== Sequence

#def[
  #align(center)[
    *infinite sequence* $X_1, X_2, ...$ is:
  ]
  - *independent* if $X_1, ..., X_n$ independent for every $n$
  - *independent and identically distributed (iid)* if independent and same distribution function ($forall i,j space F_(X_i) = F_(X_j)$)
]

=== Bernoulli Variable