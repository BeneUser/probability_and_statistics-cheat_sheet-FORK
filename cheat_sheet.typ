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

= Probability space

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

== Sigma Algebra

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

== Probability measure

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

== Terminology

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

== Laplace model

#def[
  #align(center)[*Laplace model* on $Omega$ is a triple $(Omega, F, PP)$ where]
  #spread(
    [1. $F in P(Omega)$],
    [2. $PP: F -> [0,1], forall A in F: PP[A] = (|A|) / (|Omega|)$],
  )
]

== Properties

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

= Conditional probabilities

#def[
  #align(center)[
    conditional probability of *$A$ given $B$*
    $ PP[A | B] = (PP[A inter B]) / (PP[B]) $

  ]

  #note[$ PP[B|B] = 1 $]
]

== Properties

#def[
  + $PP[.|B]$ is a *probability measure* on $Omega$
  #align(center)[$B_1, ..., B_n$ a *partition*#footnote([$Omega = B_1 union ... union B_n$ and pairwise disjoint]) of $Omega$ with $PP[B_i] > 0$]
  + $forall A in F: PP[A] = sum^n_(i=1)PP[A|B_i]PP[B_i]$ (*Formula of total probability*)
  + $PP[A>0] => PP[B_i | A ] = (PP[A|B_i]PP[B_i]) / (sum^n_(j=1)PP[A|B_j]PP[B_j])$ (*Bayes formula*)
]

= Independence

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

= Random variables

#def[
  #align(center)[
    $X$ *random variable* $<=>$ $X$ a map $X: Omega -> RR$ and $forall a in RR: {omega in Omega: X(omega) <= a} in F$
  ]
]

== Indicator Function

#def[
  #align(center)[
    *indicator function* $bb(1)_A$ of $A$:

    $ forall omega in Omega: bb(1)_A(omega) = cases(0 &"if" &omega in.not A, 1 &"if" &omega in A) $
  ]
]

= Distribution function

#def[
  #align(center)[
    *distribution function* of $X$: $ F_X: RR -> [0,1], space forall a in RR: F_X (a) = PP[X <= a] $
  ]
]

== Properties

#def[
  #columns(2)[
    + $PP[a < X <= b] = F(b) - F(a)$
    + $F$ is non-decreasing
    #colbreak()
    3. $F$ is right continuous
    + $lim_(a -> - infinity) F(a) = 0$ and $lim_(a -> infinity) F(a) = 1$
  ]
]

== Independence

#def[
  #align(center)[$X_1, ..., X_n$ *independent* $<=> forall x_1, ..., x_n in RR:$]
  $ PP[X_1 <= x_1, ..., X_n <= x_n] = PP[X_1 <= x_1] dots.c PP[X_n <= x_n] $
]

#not_relevant[
  (*grouping*) $X_1, ..., X_n$ independent, $1 <= i_1 < dots.c < i_k <= n$ indices, $phi.alt_1, ..., phi.alt_k$ functions, this is *independent*:
  $ Y_1 = phi.alt_1 (X_1, ..., X_(i_1)), ..., Y_k = phi.alt_k (X_(i_(k-1) + 1), ..., X_(i_k)) $
]

== Sequence

#def[
  #align(center)[
    *infinite sequence* $X_1, X_2, ...$ is:
  ]
  - *independent* if $X_1, ..., X_n$ independent for every $n$
  - *independent and identically distributed (iid)* if independent and same distribution function ($forall i,j space F_(X_i) = F_(X_j)$)
]

== Bernoulli Variable

#def[
  $ X ~ "Ber"(p) <=> PP[X=0] = 1 - p space "and" space PP[X=1] = p $
]

== Uniform Random Variable

#def[
  $ U ~ cal(U)([a,b]) <=> F_U = cases(0 space.quad &x < a, x space.quad &a <= x <= b, 1 space.quad &x > b) $
]

== Inverse Transform Sampling

#def[
  $ U ~ cal(U)([0,1]), F: RR -> [0,1] "a distribution function" \ => X = F^(-1)(U) "has distribution" F_X = F $

  #note[
    This also applies to a *sequence of functions* and independent random variables.
  ]
]

= Discrete and Continuous Random Variables

#def[
  $ PP[X=a] = F(a) - F(a-) $
]

#def[
  $ A "occurs" #strong("almost surely (a.s.)") <=> PP[A] = 1 $
]

== Discrete Random Variables

#def[
  $ X: Omega -> RR #strong("discrete") \ <=> exists W subset RR "finite or countable": X in W "a.s." $
]

=== Distribution

#def[
  $ (p(x))_(x in W) #strong("distribution of") X <=> forall x in W: p(x) := PP[X=x] $
]

#def[
  $ sum_(x in W) p(x) = 1 $
]

#def[
  $ forall x in RR: F_X(x) = attach(sum, tr: y<=x, br: y in W)p(x) $
]

=== Distributions

#note[
  #align(center)[see at the end for the distribution table]
]

==== Bernoulli

#def[
  $ "Bin"(1,p) = "Ber"(p) $
]

#def[
  $ X ~ "Bin"(m,p), space Y ~ "Bin"(n,p), space X,Y "independent" \ => X + Y ~ "Bin"(m+n, p) $
]

==== Geometric

#def[
  #align(center)[$X_1, X_2, ...$ a sequence of infinite, independent Bernoulli, then:]
  #align(center)[$T:= min{n >= 1: X_n = 1}$ geometric with parameter $p$]
]

#def[
  $ forall n >= 0, k >=1 space.quad PP[T >= n + k | T > n] = PP[T >= k] $
]

== Continuous random variables

#def[
  $
    X: Omega -> RR #strong("continuous") <=> \ "distribution" F_X (a) = integral^a_(- infinity) f(x) d x space.quad "for all" a in RR \ "for some non-negative" #strong("density") f: RR -> RR_+
  $
]

#def[
  $ integral^(+infinity)_(-infinity) f(x) d x = 1 $
]

#def[
  $ F_X (x) = integral^x_(-infinity) f(y) d y $
]

#def[
  $
    F_X "continuous, piecewise" C^1 (F_X "is" C_1 "on all" (x_i, x_(i+1))) \ => forall x in (x_i, x_(i+1)) space.quad f(x) = F'_X(x) \ "with arbitrary" x_1, ..., x_(n-1)
  $
]

=== Distributions

#note[
  #align(center)[see at the end for the distribution table]
]

==== Uniform

#def[
  $ PP[X in [c, c+lambda]] = l / (b-a) $
]

==== Exponential

#def[
  $ forall t space.quad PP[T > t] = e^(- lambda t) $
]

#def[
  $ forall t, s >= 0 space.quad PP[T > t + s | T > t] = PP[T > s] $
]

#def[
  $ PP[T > t + s | T > t] = e^(- lambda s) $
]

==== Normal

#def[
  $
    X_1, ..., X_n "independent, parameters:" (m_1, sigma^2_1), ..., (m_n, sigma^2_n) \ => Z = m_0 + lambda_1 X_1 + ... + lambda_n X_n "normal, parameters:" \ m = m_0 + lambda_1 m_1 + ... + lambda_n m_n "and" sigma^2 = lambda_1^2 sigma^2_1 + ... + lambda_n^2 sigma^2_n
  $
]

#def[
  $ X ~ cal(N)(0,1) #strong("standard normal") \ => Z = m + sigma dot.c X "normal, parameters:" m "and" sigma^2 $
]

#def[
  $ PP[| X - m | >= 3 sigma] <= 0.0027 $
]

#pagebreak()

= Formula Collection

#page(columns: 1)[
  == Distributions
  #show table.cell.where(x: 0): strong
  #show table.cell.where(y: 0): strong

  #table(
    fill: (x, y) => if y == 0 { luma(80%) } else { },
    columns: (auto, auto, auto, auto, auto, auto, auto, 1fr),
    align: (
      left + horizon,
      left + horizon,
      left + horizon,
      center + horizon,
      center + horizon,
      center + horizon,
      center + horizon,
      left + horizon,
    ),
    inset: (x: 5pt, y: 7pt),
    table.header(
      [Distribution],
      [Notation],
      [Parameters],
      [$EE[X]$],
      [$"Var"(X)$],
      [$p_X(t) "/" f_X(t)$],
      [$F_X(t)$],
      [Use Case],
    ),

    table.cell(colspan: 8, align: center + horizon)[Discrete Distributions],

    [Equal Distribution],
    [unknown],
    [$n$: Event Count \ ($x_i$: Events)],
    [$1 / n sum^n_(i=1)x_i$],
    [$1 / n sum^n_(i=1) x^2_i - 1 / (n^2) (sum^n_(i=1) x_i)^2$],
    [$1 / n$],
    [$(|{k:x_k <= t}|) / n$],
    [uniform discrete, equal chance, coin toss, dice],

    [Bernoulli],
    [$"Ber"(p)$],
    [$p:$ Success Probability],
    [$p$],
    [$p(1-p)$],
    [$p^t (1-p)^(1-t)$],
    [$1-p "for" 0 <= t < 1$],
    [single trial, success/failure, coin flip],

    [Binomial],
    [$"Bin"(n,p)$],
    [$n$: Event Count \ $p$: Success Probability],
    [$n p$],
    [$n p (1-p)$],
    [$vec(n, t) p^t (1-p)^(n-t)$],
    [$sum^t_(k=0) vec(n, k) p^k (1-p)^(n-k)$],
    [repeated trials, number of successes, binary outcomes],

    [Geometric],
    [$"Geom"(p)$],
    [$p$: Success Probability \ ($t$: Event Count)],
    [$1 / p$],
    [$(1-p) / (p^2)$],
    [$p (1-p)^(t-1)$],
    [$1 - (1-p)^t$],
    [trials until first success, waiting time],

    [Poisson],
    [$"Poisson"(lambda)$],
    [$lambda$: $EE[X] "and" "Var"(X)$],
    [$lambda$],
    [$lambda$],
    [$(lambda^t) / (t!) e^(- lambda)$],
    [$e^(- lambda) sum^t_(k=0) (lambda^k) / (k!)$],
    [rare events, fixed interval, error count],

    [Hypergeometric],
    [$H(n,r,m)$],
    [$n in NN, m,r in {1,...,n}$],
    [$m r / n$],
    [$m r / n (1 - r / n) (n-m) / (n-1)$],
    [$(vec(r, k)vec(n-r, m-k)) / vec(n, m)$],
    [$sum^k_(y=0) (vec(r, y)vec(n-r, m-y)) / (vec(n, m))$],
    [sampling without replacement, finite population],

    [Negative Binomial],
    [$"NBin"(r,p)$],
    [$r in NN, p in [0,1]$],
    [$r / p$],
    [$(r(1-p)) / (p^2)$],
    [$vec(k-1, r-1) p^r (1-p)^(k-r)$],
    [too complicated],
    [count until $r$ successes, aggregated counts],

    table.cell(colspan: 8, align: center + horizon)[Continuous Distributions],

    [Uniform],
    [$U ~ cal(U)([a,b])$],
    [$[a,b]$: Interval],
    [$(a+b) / 2$],
    [$1 / 12 (b-a)^2$],
    [$cases(1 / (b-a) space.quad &a <= x <= b, 0 space.quad &"otherwise")$],
    [$cases(0 space.quad &x <= a, (t-a) / (b-a) space.quad &a < x < b, 1 space.quad &x >= b)$],
    [equal probability, continuous interval, random selection],

    [Exponential],
    [$"Exp"(lambda)$],
    [$lambda$: $1 / (EE[X])$],
    [$1 / lambda$],
    [$1 / (lambda^2)$],
    [$cases(lambda e^(- lambda t) space.quad &t >= 0, 0 space.quad &t < 0)$],
    [$cases(1 - e^(- lambda t) space.quad &t > 0, 0 space.quad &t <= 0)$],
    [time between events, memoryless, lifetimes],

    [Normal],
    [$cal(N)(mu, sigma^2)$],
    [$mu$: $EE[X]$ \ $sigma^2$: $"Var"(X)$],
    [$mu$],
    [$sigma^2$],
    [$1 / (sqrt(2 pi sigma^2)) e^(- ((t - mu)^2) / (2 sigma^2))$],
    [$1 / (sigma sqrt(2 pi)) integral^t_(- infinity) e^(- 1 / 2 ((y - mu) / sigma)^2) d y$],
    [bell curve, natural variation, central limit],

    [$cal(X)^2$],
    [$cal(X)^2_m$],
    [$n$: Freedom Degree],
    [$n$],
    [$2n$],
    [$1 / (2^(n / 2) Gamma (n / 2)) t^(n / 2 - 1) e^(- t / 2) "for" t > 0$],
    [$P(n / 2, t / 2)$],
    [goodness-of-fit, independence test, hypothesis testing],

    [Student's $t$],
    [$t_m$],
    [$n$: Freedom Degree],
    [$cases(0 space.quad &n > 1, "undef." space.quad &"otherwise")$],
    [$cases(n / (n-2) space.quad &n > 2, infinity space.quad &1 < n <= 2, "undef." space.quad &"otherwise")$],
    [$(Gamma ((n+1) / 2)) / (sqrt(n pi) Gamma (n / 2)) (1 + (t^2) / n)^(- (n+1) / 2)$],
    [too complicated],
    [small samples, unknown variance, confidence intervals],

    [Cauchy],
    [$"Cauchy"(x_0, gamma)$],
    [$x_0 in RR, gamma > 0$],
    [does not exist],
    [does not exist],
    [$1 / pi gamma / (gamma^2 + (x - x_0)^2)$],
    [$1 / 2 + 1 / pi arctan ((x - x_0) / gamma)$],
    [heavy tails, undefined mean/variance, physics/finance],
  )
]
