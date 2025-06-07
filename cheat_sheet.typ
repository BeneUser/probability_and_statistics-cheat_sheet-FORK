#import "@preview/cetz:0.3.1"
#import "@preview/cetz-plot:0.1.0": *

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

#let _block = block.with(inset: 6pt, radius: 2pt, width: 100%, breakable: true, stroke: black);
#let def(body) = _block(body, stroke: blue)
#let note(body) = _block(body, stroke: orange)
#let form(body) = _block(body, stroke: black)
#let not_relevant(body) = _block(body, stroke: (paint: gray, dash: "dashed"))
#let example(body) = _block(body, stroke: purple)

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
    #note[Notes, Remarks]
    #example[Examples]

    #colbreak()

    #form[Formulas]
    #not_relevant[Not Relevant]
  ],
)

= Probability Space

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

== Probability Measure

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

== Laplace Model

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

= Conditional Probabilities

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

= Random Variables

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

= Distribution Function

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

== Continuous Random Variables

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

= Expectation

#def[
  $ EE[X] = integral^infinity_0 (1 - F_X(x)) d x $

  #note[
    #columns(2)[
      + $X: Omega -> RR_+$
      + can be finite or infinite
      #colbreak()
      3. $EE[X] >= 0 space.quad (X > 0)$
      + $X=0 "a.s." => EE[X] = 0$
    ]
  ]
]

#def[
  $ EE[ |X| ] <= infinity => EE[X] = EE[X_+] - EE[X_-] $

  #note[
    $
      X_+ (omega) &= cases(X(omega) space.quad &"if" &X(omega) >= 0, 0 &"if" &X(omega) < 0) \ X_-(omega) &= cases(-X(omega) space.quad &"if" &X(omega) <= 0, 0 &"if" &X(omega) > 0)
    $
    $ X = X_+ - X_- space.quad "and" space.quad |X| = X_+ + X_- $
  ]
]

== Discrete

#def[
  $ EE[X] = sum_(x in W) x dot.c PP[X = x] "and" EE[phi.alt (X)] = sum_(x in W) phi.alt (x) dot.c PP[X=x] $
]

== Continuous

#def[
  $
    EE[X] = integral^infinity_(-infinity) x dot.c f(x) d x space.quad "and" space.quad EE[phi.alt (X)] = integral^infinity_(-infinity) phi.alt (x) f(x) d x
  $
]

== Calculus

#def[
  $ EE[lambda X] = lambda EE[X] space.quad "and" space.quad EE[X+Y] = EE[X] + EE[Y] $
]

#def[
  $ X "and" Y "independent" => EE[X Y] = EE[X] EE[Y] $
]

== Tailsum

#def[
  $ PP[X >= 0] = 1 => EE[X] = integral^infinity_0 PP[X>x] d x $
]

#def[
  $ X subset.eq NN => EE[X] = sum^infinity_(n=1) PP[X >= n] $
]

== Density

#def[
  #align(center)[if $integral^(+infinity)_(- infinity) f(x) d x = 1$ then those are equivalent:]
  + $X$ is continuous with density $f$
  + $forall phi.alt: RR -> RR$ piecewise continuous, bounded: $ EE[phi.alt (X)] = integral^infinity_(-infinity) phi.alt (x) f(x) d x $
]

== Independence

#def[
  $
    X_1, ..., X_n "independent" <=> \ forall phi.alt_1 : RR -> RR, ..., phi.alt_n : RR -> RR "piecewise continuous, bounded:" \ EE[phi.alt_1 (X_1) dots.c phi.alt_n (X_n)] = EE[phi.alt_1 (X_1)] dots.c EE[phi.alt_n (X_n)]
  $
]

== Inequalities

=== Monotonicity

#def[
  $ X <= Y "a.s." => EE[X] <= EE[Y] $
]

=== Markov

#def[
  $ X >= 0 => forall a > 0: PP[X>=a] <= (EE[X]) / a $
]

=== Jensen

#def[
  $ phi.alt "konvex" => phi.alt (EE[X]) <= EE[phi.alt (X)] $

  #note[
    #columns(2)[
      - $|EE[X| <= EE[|X|]$
      #colbreak()
      - $EE[|X|] <= sqrt(EE[X^2])$
    ]
  ]
]

= Variance

#def[
  $ EE[X^2] < infinity => "Var"(X) = sigma_X^2 = EE[(X-m)^2], m = EE[X] $
  $ sigma_X = #strong("standard deviation") $

  #note[
    #align(center)[indicator of fluctuations around $m = EE[X]$]
  ]
]

#def[
  $ EE[X^2] < infinity: $
  - $forall a >= 0: PP[ |X-m| >= a] <= (sigma^2_X) / (a^2), space.quad m = EE[X]$
  - $sigma_X^2 = EE[X^2] - EE[X]^2$
  - $lambda in RR => sigma^2_(lambda X) = lambda^2 dot.c sigma^2_X$
  - $X_1, ..., X_n "pairwise independent", S = X_1, ..., X_n => sigma^2_S = sigma^2_(X_1) + ... + sigma^2_(X_n)$
]

= Covariance

#def[
  $ "Cov"(X,Y) = EE[X Y] - EE[X] EE[Y] $

  #note[
    #align(center)[quantifies the dependence between two random variables]
  ]
]

#def[
  $ X,Y "independent" => "Cov"(X,Y) = 0 $
]

#def[
  $ X,Y "independent" <=> \ forall phi.alt, psi "piecewise continuous, bounded" "Cov"(phi.alt (X), psi (Y)) = 0 $
]

= Joint Distribution

== Discrete

#def[
  $
    X_1, ..., X_n "discrete", X_i in W_i "a.s.", W_i subset RR "finite or countable:" \ p(x_1, ..., x_n) = PP[X_1 = x_1, ..., X_n = x_n]
  $
]

#def[
  $ sum_(x_1 in W_1, ..., x_n in W_n) p(x_1, ..., x_n) = 1 $
]

#def[
  $
    Z = phi.alt (X_1, ..., X_n), W = phi.alt (W_1 times dots.c W_n): \ forall z in W: PP[Z = z] = sum^(x_1 in W_1, ..., x_n in W_n)_(phi.alt (x_1, ..., x_n) = z) PP[X_1 = x_1, ..., X_n = x_n]
  $
]

=== Marginal Distributions

#def[
  $
    forall z in W_i: PP[X_i = z] = \ sum_(x_1, ..., x_(i-1), x_(i+1), ..., x_n) p(x_1, ..., x_(i-1), z, x_(i+1), ..., x_n)
  $
]

=== Expectation of the Image

#def[
  $ EE[phi.alt (X_1, ..., X_n)] = sum_(x_1, ..., x_n) phi.alt (x_1, ..., x_n) p(x_1, ..., x_n) $
]

=== Independence

#def[
  $
    X_1, ..., X_n "independent" <=> \ p(x_1, ..., x_n) = PP[X_1 = x_1] dots.c PP[X_n = x_n] \ "for every" x_1 in W_1, ..., x_n in W_n
  $
]

== Continuous

=== Joint Density

#def[
  $
    PP[X_1 <= a_1, ..., X_n <= a_n] = integral^(a_1)_(-infinity) dots.c integral^(a_n)_(-infinity) f(x_1, ..., x_n) d x_n dots.c d x_1
  $
]

#def[
  $ integral^(infinity)_(-infinity) dots.c integral^(infinity)_(-infinity) f(x_1, ..., x_n) d x_n dots.c d x_1 = 1 $
]

=== Expectation of the Image

#def[
  $
    EE[phi.alt (X_1, ..., X_n)] = \ integral^infinity_(-infinity) dots.c integral^infinity_(-infinity) phi.alt (x_1, ..., x_n) dot.c f(x_1, ..., x_n) d x_n dots.c d x_1
  $
]

=== Marginal Densities

#def[
  $
    f_i (z) = integral_((x_1,...,x_(i-1), x_(i+1), ..., x_n) in RR^(n-1)) f(x_1, ..., x_(i-1), z, x_(i+1), ..., x_n) \ d x_1 dots.c d x_(i-1) d x_(i+1) dots.c d x_n
  $
]

=== Independence

#def[
  $
    X_1, ..., X_n "independent" <=> X_1, ..., X_n "jointly continuous" \ "with" f(x_1, ..., x_n) = f_1 (x_1) dots.c f_n (x_n)
  $
]

= Asymptotic Results

#def[
  $ S_n / n = (X_1 + ... + X_n) / n = #strong("empirical average") $

  #note[
    $ X_i "are i.i.d"#footnote("independent and identically distributed") $
  ]
]

== Law of Large Numbers

#def[
  $ lim_(n -> infinity) (X_1 + ... + X_n) / n = m = EE[X_1] $
]

== Monte-Carlo Integration

#def[
  #align(center)[Goal: Calculate $I = integral^1_0 g(x) d x$. \ #line(length: 90%)]
  $
    EE[g(U)] = integral^1_0 g(x) d x = 1, U ~ cal(U)([0,1]) \ => lim_(n -> infinity) (g(U_1) + ... + g(U_n)) / n = I = EE[ |X_1| ], X_n = g(U_n) \ => "get I by calculating" \ (g(U_1) + ... + g(U_n)) / n "for large n, simulate" U_i
  $
]

== Convergence in Distribution

#def[
  $
    X_n attach(approx, t: "Approx") X "as" n -> infinity \ "if for every" x in RR \ lim_(n -> infinity) PP[X_n <= x] = PP[X <= x]
  $
]

== Central Limit Theorem

#def[
  $
    m = EE[X_1], sigma^2 = "Var"(X_1), S_n = sum^n_(i=1) X_i, Phi = cal(N)(0,1) => \ PP[(S_n - n m) / sqrt(sigma^2 n) <= a] arrow.r.long_(n -> infinity) Phi (a) = 1 / sqrt(2 pi) integral^a_(- infinity) e^(-x^2 / 2) d x
  $

  #note[
    $ Z_n attach(approx, t: "Approx") Z "as" n -> infinity $
    $ EE[Z_n = 0] space.quad "and" space.quad "Var"(Z_n) = 1 $
    $ lim_(n -> infinity) PP[n m - 2 sqrt(sigma^2 n) <= S_n <= m n + 2 sqrt(sigma^2 n)] = p tilde.eq 95% $
  ]
]

= Estimators

#def[
  #align(center)[
    Estimate unknown parameter $theta$ based on sample $X_1, ..., X_n$
  ]
]

#def[
  $ T: Omega -> RR #strong("Estimator") "with" T = t(X_1, ..., X_n) \ t: RR^n -> RR "measurable function" $
  $ t(x_1, ..., x_n) = "estimate for observed data" x_1, ..., x_n "for" theta $
]

== Bias and Mean Squared Error

#def[
  $ T "unbiased for" theta <=> forall theta in Theta: EE_theta [T] = theta $
]

#def[
  $ "Bias"_theta (T) = EE_theta [T] - theta $
  $ "MSE"_theta (T) = EE_theta [(T-theta)^2] $
  $ "MSE"_theta (T) = "Var"_theta (T) + ("Bias"_theta (T))^2 $
]

== Maximum Likelihood Estimation (MLE)

=== Likelihood Function

#def[
  $
    L(x_1, ..., x_n ; theta) = cases(product^n_(i=1) p_(X_i) (x_i ; theta) space.quad &"if" X_i "are discrete", product^n_(i=1) f_(X_i) (x_i ; theta) &"if" X_i "are continuous")
  $
]

=== Maximum Likelihood Estimator (MLE)

#def[
  $ hat(theta)_"ML" (x_1, ..., x_n) in arg max_(theta in Theta) L(x_1, ..., x_n ; theta) $
]

==== Log-Likelihood Function

#def[
  $ l(theta ; x_1, ..., x_n) = log L (x_1, ..., x_n ; theta) $
  $ T_"ML" = t_"ML" (X_1, ..., X_n) $

  #note[
    #align(center)[
      find maximum = derivation is 0 \ use logarithm because it's easier to differentiate \ this also works for more dimensions
    ]
  ]
]

= Confidence Intervals

#def[
  #align(center)[
    $alpha in [0,1], space a,b: RR^n -> RR, space A = a(X_1, ..., X_n), space B = b(X_1, ..., X_n)$

    *confidence interval* for $theta$ with confidence level $1 - alpha :=$

    $ I = [A,B], space "such that for all" theta in Theta: PP_theta [A <= theta <= B] >= 1 - alpha $
  ]
]

== Distribution Statements

=== $cal(X)^2$

#note[
  #align(center)[
    see distribution table below for more
  ]
]

#def[
  $ Gamma (v) = integral^infinity_0 t^(v-1) e^(-t) d t $
  $ n in NN => Gamma (n) = (n-1)! $
]

#def[
  $ X_1, ..., X_m "i.i.d" ~ cal(N)(0,1) => Y = sum^m_(i=1) X^2_i ~ cal(X)^2_m $
]

=== t

#def[
  $ X ~ N(0,1), space Y ~ cal(X)^2_m => Z := X / sqrt(Y / m) ~ t_m $
]

== Normal Model with Unknown Variance and Mean

#def[
  $ dash(X)_n = 1 / n sum^n_(i=1) X_i, space S^2 = 1 / (n-1) sum^n_(i=1) (X_i - dash(X)_n)^2 $
  $ X_1, ..., X_n "i.i.d" ~ N(m, sigma^2) => dash(X)_n, space S^2 "independent" $
]

== Approximate Confidence Intervals

#def[
  #align(center)[
    Often, estimator $T$ is a sum ($T = 1 / n sum^n_(i=1) Y_i$). One can use the CLT (for large $n$): $sum^n_(i=1) Y_i approx N(n EE[Y_i], n "Var"[Y_i])$
  ]
]

= Tests

== Null and Alternative Hypotheses

#def[
  $ "Null Hypothesis" H_0: theta in Theta_0 $
  $ "Alternative Hypothesis" H_A: theta in Theta_A $

  #note[
    $ Theta_0 inter Theta_A = emptyset, "often" Theta_A = Theta backslash Theta_0 $

    #align(center)[
      When $Theta_0$ or $Theta_A$ only have one value, they are called *simple*, else *composite*.

      The statement we want to prove lies in $Theta_A$.
    ]
  ]
]

== Tests and Decisions

#def[
  #align(center)[
    Test = pair $(T,K)$ where
  ]
  - $T$ a statistic, $T = t(X_1, ..., X_n)$
  - $K subset RR$ a (deterministic) set, called *critical region*

  #line()

  $ T(omega) = t(x_1, ..., x_n) "(observed data)" $
  $ cases("Reject" H_0 space.quad &"if" T(w) in K, "Do not reject" H_0 &"if" T(omega) in.not K) $
]

=== Errors

#def[
  / Type 1: $H_0$ rejected, but its true. Probability $PP_theta [T in K]$
  / Type 2: $H_0$ not rejected, but is false. Probability $1 - PP_theta [T in K]$

  #note[
    #align(center)[Goal: Minimize Type 1 Error]
  ]
]

== Significance Level and Power

#def[
  $ (T, K) "has significance level" alpha <=> forall theta in Theta_0: PP_theta [T in K] <= alpha $
]

#def[
  $ "power of" (T,K) := beta: Omega_A -> [0,1], space theta |-> beta (theta) := PP_theta [T in K] $
]

#note[
  1. Minimize Significance Level $=>$ Minimize Type 1 Error
  2. Maximize Power $=>$ Minimize Type 2 Error
]

== Construction of Tests

=== Likelihood Ratio

#def[
  $ R(x_1, ..., x_n) = (L(x_1, ..., x_n ; theta_A)) / (L(x_1, ..., x_n ; theta_0)) $

  #note[
    $ L(x_1, ..., x_n ; theta_0) = 0 => R(x_1, ..., x_n) = +infinity $

    #align(center)[
      If ration is large $=>$ observations are more likely under the alternative than the hypothesis
    ]
  ]
]

=== Likelihood Ratio Test

#def[
  $ (T,K) "with" T = R(X_1, ..., X_n), space K = (c, infinity), c >= 0 $

  #note[
    #align(center)[
      Any other test with significance level no greater than the level of the likelihood ratio test will have *lower power* (i.e., a higher probability of a Type II error)
    ]
  ]
]

==== General

#def[
  $
    R(x_1, ..., x_n) = (sup_(theta in Theta_A) L(x_1, ..., x_n ; theta)) / (sup_(theta in Theta_0) L(x_1, ..., x_n ; theta))
  $

  #note[
    #align(center)[
      for composite $Theta$'s
    ]
  ]
]

== p-value

#def[
  $ (T, (K_t)_(t>=0)) "ordered with respect to" T <=> \ forall s,t >= 0: s <= t => K_s supset K_t $
]

#def[
  $
    K_t = (t, infinity) "(right-tailed test)" \ K_t = (-infinity, -t) "(left-tailed test)" \ K_t = (-infinity, -t) union (t, infinity) "(two-sided test)"
  $
]

#def[
  $ "p-value" = G(t), space G: RR^+ -> [0,1], G(t) = PP_(theta_0) [T in K] $

  #note[
    The p-value informs us which tests in our family ${(T, K t ) : t >= 0}$ would lead to rejection of $H_0$ . In fact, if the observed p-value is $p$, then every test with significance level $alpha > p$ would reject $H_0$ and those with $alpha <= p$ would not.
  ]
]

#pagebreak()

= Formula Collection

#show math.equation: set block(breakable: true) // equations in the collection should wrap pages

=== Unit Circle

#form()[
  #context {
    set align(center)
    set text(size: 10pt)

    cetz.canvas(
      length: 2.5cm,
      {
        import cetz.draw: *

        let entries = (
          (0deg, $0$),
          (15deg, $pi / 12$),
          (30deg, $pi / 6$),
          (45deg, $pi / 4$),
          (60deg, $pi / 3$),
          (75deg, $(5pi) / 12$),
          (90deg, $pi / 2$),
          (105deg, $(7pi) / 12$),
          (120deg, $(2pi) / 3$),
          (135deg, $(3pi) / 4$),
          (150deg, $(5pi) / 6$),
          (165deg, $(11pi) / 12$),
          (180deg, $pi$),
          (195deg, $(13pi) / 12$),
          (210deg, $(7pi) / 6$),
          (225deg, $(5pi) / 4$),
          (240deg, $(4pi) / 3$),
          (255deg, $(17pi) / 12$),
          (270deg, $(3pi) / 2$),
          (285deg, $(19pi) / 12$),
          (300deg, $(5pi) / 3$),
          (315deg, $(7pi) / 4$),
          (330deg, $(11pi) / 6$),
          (345deg, $(23pi) / 12$),
        )

        set-style(mark: (fill: black, scale: 2), stroke: (thickness: 0.4pt, cap: "round"), content: (padding: 1pt))

        let inner_factor = 1.15 // factor by which cos/sin are scaled for the inner text ring
        let outer_factor = 1.35 // factor by which cos/sin are scaled for the outer text ring

        for (deg, label) in entries {
          let text_angle = if deg < 180deg { deg - 90deg } else { deg + 90deg }

          line(
            (0, 0),
            (calc.cos(deg), calc.sin(deg)),
            stroke: (dash: "dashed"),
          )
          content((calc.cos(deg) * inner_factor, calc.sin(deg) * inner_factor), label, angle: text_angle)
          content(
            (calc.cos(deg) * outer_factor, calc.sin(deg) * outer_factor),
            $ #calc.round(deg.deg())° $,
            angle: text_angle,
          )
        }

        circle((0, 0), radius: 1)

        line((-1, 0), (1, 0))
        line((0, -1), (0, 1))
      },
    )
  }

  #columns(2)[
    #figure(image("images/unit_circle.svg", width: 100%))
    #colbreak()
    #figure(image("images/unit_triangle.svg", width: 100%))
  ]

  *Sources:* #link("https://commons.wikimedia.org/w/index.php?curid=11434668")[Wiki Commons: Dnu72, Pengo] and #link("https://commons.wikimedia.org/wiki/File:Sinus_und_Kosinus_am_Einheitskreis_Einfach_Cos.svg")[Wiki Commons: Yomomo]
]

=== Pythagoras

#form()[
  Let $a$ be the adjacent, $b$ be the opposite and $c$ be the hypotenuse. Then:

  $ a^2 + b^2 = c^2 $
]

=== Trigonometric Functions

#form()[
  $
    sin (alpha) = "opposite" / "hypotenuse" space.quad space.quad cos (alpha) = "adjacent" / "hypotenuse" \
    tan (alpha) = (sin (alpha)) / (cos (alpha)) = "opposite" / "adjacent" \
    cot (alpha) = (1) / (sin (alpha)) = "hypotenuse" / "opposite" \
    sec (alpha) = (1) / (cos (alpha)) = "hypotenuse" / "adjacent" \
  $
]

=== Trigonometric Values

#form()[
  $ + pi <=> dot -1 $

  #table(
    columns: (1fr, 1fr, 1fr, 1fr, 1fr),
    table.header([*deg*], [*rad*], [*sin*], [*cos*], [*tan*]),
    stroke: (x, y) => if y == 0 {
      (bottom: 0.7pt + black)
    },
    $0 degree$, $0$, $0$, $1$, $0$,
    $30 degree$, $pi / 6$, $1 / 2$, $sqrt(3) / 2$, $sqrt(3) / 3$,
    $45 degree$, $pi / 4$, $sqrt(2) / 2$, $sqrt(2) / 2$, $1$,
    $60 degree$, $pi / 3$, $sqrt(3) / 2$, $1 / 2$, $sqrt(3)$,
    $90 degree$, $pi / 2$, $1$, $0$, $"N/A"$,
    $120 degree$, $(2 pi) / 3$, $sqrt(3) / 2$, $- 1 / 2$, $- sqrt(3)$,
    $135 degree$, $(3 pi) / 4$, $sqrt(2) / 2$, $- sqrt(2) / 2$, $-1$,
    $150 degree$, $(5 pi) / 6$, $1 / 2$, $- sqrt(3) / 2$, $- 1 / sqrt(3)$,
    $180 degree$, $pi$, $0$, $-1$, $0$,
  )
]

=== Trigonometric Identities

#form()[
  ==== Inverse

  $
    cos (x) = cos (-x) , space - sin (x) = sin (-x) \
    cos (pi - x) = -cos (x) , space sin (pi - x) = sin (x), space |sin (x)| lt.eq.slant x
  $

  ==== Doubled Angles

  $
    sin (2 alpha) = 2 sin (alpha) cos (alpha) \
    cos ( 2 alpha) = cos^2 (alpha) - sin^2 (alpha) = 1 - 2 sin^2 (alpha) \
    tan (2 alpha) = (2 tan (alpha)) / (1 - tan^2 (alpha))
  $

  ==== Addition / Subtraction

  $
    sin (alpha plus.minus beta) = sin (alpha) cos (beta) plus.minus cos (alpha) sin (beta) \
    cos (alpha plus.minus beta) = cos (alpha) cos (beta) minus.plus sin (alpha) sin (beta) \
    tan (alpha plus.minus beta) = (tan (alpha) plus.minus tan (beta)) / (1 minus.plus tan (alpha) tan (beta))
  $

  ==== Multiplication

  $
    sin (alpha) sin (beta) &= - (cos (alpha + beta) - cos (alpha - beta)) / 2 \
    cos (alpha) cos (beta) &= (cos (alpha + beta) + cos (alpha - beta)) / 2 \
    sin (alpha) cos (beta) &= (sin (alpha + beta) + sin (alpha - beta)) / 2
  $

  ==== Powers

  $
    sin^2 (alpha) &= 1 / 2 (1 - cos (2 alpha)) \
    sin^3 (alpha) &= (3 sin (alpha) - sin (3 alpha)) / 4 \
    cos^2 (alpha) &= 1 / 2 (1 + cos (2 alpha)) \
    cos^3 (alpha) &= (3 cos (alpha) - cos (3 alpha)) / 4 \
    tan^2 (alpha) &= (1 - cos ( 2 alpha)) / (1 + cos (2 alpha)) \
    sin^2 (alpha) cos^2 (alpha) &= (1 - cos (4 alpha)) / 8
  $

  ==== Divers

  $
    sin^2 (alpha) + cos^2 (alpha) &= 1 \
    cosh^2 (alpha) - sinh^2 (alpha) &= 1 \
    sin (z) &= (e^(i z) - e^(- i z)) / (2 i) \
    cos (z) &= (e^(i z) + e^(- i z)) / 2 \
    tan (x) = (sin (x)) / (cos (x)) &, space cot (x) = (cos (x)) / (sin (x)) \
    sin (arctan (x)) &= x / sqrt(x^2 + 1) \
    cos (arctan (x)) &= 1 / sqrt(x^2 + 1) \
    sin (x) &= (tan (x)) / sqrt(1 + tan^2 (x)) \
    cos (x) &= 1 / sqrt(1 + tan^2 (x)) \
    cosh (x)^k &= cosh (x) "for even" k \
    cosh (x)^k &= sinh (x) "for odd" k
  $
]

=== Midnight / Quadratic Formula

#form()[
  ==== General ($a x^2 + b x + c = 0$)
  #columns(2)[
    $ x = (-b plus.minus sqrt(b^2 - 4 a c)) / (2 a) $
    #colbreak()
    $ b^2 - 4 a c < 0 \ => x "complex" $
  ]

  === Simple ($x^2 + p x + q = 0$)
  #columns(2)[
    $ x = -p / 2 plus.minus sqrt((p / 2)^2 - q) $
    #colbreak()
    $ (p / 2)^2 - q < 0 \ => x "complex" $
  ]
]

=== Logarithm Rules

#form()[
  $
    log_b (x dot y) &= log_b (x) + log_b (y) \
    log_b (x / y) &= log_b (x) - log_b (y) \
    log_b (x^p) &= p log_b (x) \
    log_b (root(p, x)) &= (log_b (x)) / p \
    log_b (a) &= (log_k (a)) / (log_k (b)) = (ln (a)) / (ln (a)) \
    ln (1) = 0 &, space ln (e) = 1
  $
]

=== Exponential Rules

#form()[
  $
    e^(x) e^(y) &= e^(x + y) \
    e^(x) &gt 1, space.quad x > 0 \
    x^a &= e^(a dot ln (x)) \
    e^(i z) &= cos (z) + i sin (z) \
    e^((i pi) / 2) = i, space e^(i pi) &= -1, space e^(2i pi) = 1
  $
]

=== Differentiation Rules

#form()[
  $
    (a f plus.minus b g)' &= a f' plus.minus b g' \
    (f g)' (x) &= f' (x) g(x) + f (x) g' (x) \
    (f (g (x)))' &= f' (g (x)) dot g' (x) \
    g' &= 1 / (f' compose g), space.quad g = f^(-1) \
    (1 / f(x))' &= - (f' (x)) / (f (x))^2 \
    (f / g)' &= (f' g - g' f) / g^2 \
    (a^f)' &= ln (a) dot a^f dot f'
  $
]

=== Integration Rules

#form()[
  $
    F(x) &= integral_a^x f(t) d t, space.quad F'(x) = f(x) \
    integral^b_a f(x) d x &= F(b) - F(a) \
    integral (a f plus.minus b g) d x &= a integral f d x plus.minus b integral g d x \
    integral x^n d x &= (x^(n+1)) / (n + 1) + C \
    integral f dot g' d x &= f dot g - integral f' g d x \
    F compose Phi (u) &= integral f(Phi (u)) Phi ' (u) d u \
    f(-x) = f(x) &=> integral^a_(-a) f(x) d x = 2 integral_0^a f(x) d x \
    f(-x) = -f(x) &=> integral^a_(-a) f(x) d x = 0 \
  $
]

=== Differentials / Integrals

#form()[
  #table(
    columns: (1fr, 1fr),
    table.header([*$F(x)$*], [*$F'(x) = f(x)$*]),
    stroke: (x, y) => {
      if y == 0 {
        (bottom: 0.7pt + black)
      }
      if (x == 0) {
        (right: 0.7pt + black)
      }
    },
    $c$, $0$,
    $x^a$, $a dot x^(a-1)$,
    $1 / (a + 1) x^(a+1)$, $x^a$,
    $1 / (a dot (n+1)) (a x + b)^(n+1)$, $(a x + b)^n$,
    $(x^(alpha + 1)) / (alpha + 1)$, $x^alpha , space alpha != -1$,
    $sqrt(x)$, $1 / (2 sqrt(x))$,
    $root(n, x)$, $1 / n x^(1 / n - 1)$,
    $2 / 3 x^(2 / 3)$, $sqrt(x)$,
    $n / (n+1) x^(1 / n + 1)$, $root(n, x)$,
    $e^x$, $e^x$,
    $ln (|x|)$, $1 / x$,
    $log_a (|x|)$, $1 / (x ln (a)) = log_a (e) 1 / x$,
    $sin (x)$, $cos (x)$,
    $cos (x)$, $- sin(x)$,
    $tan (x)$, $1 / (cos^2 (x)) = 1 + tan^2 (x)$,
    $cot (x)$, $1 / (- sin^2 (x))$,
    $arcsin (x)$, $1 / sqrt(1 - x^2)$,
    $arccos (x)$, $-1 / sqrt(1 - x^2)$,
    $arctan (x)$, $1 / (1 + x^2)$,
    $sinh (x)$, $cosh (x)$,
    $cosh (x)$, $sinh (x)$,
    $tanh (x)$, $1 / (cosh^2 (x)) = 1 - tanh^2 (x)$,
    $"arcsinh" (x)$, $1 / sqrt(1+x^2)$,
    $"arccosh" (x)$, $1 / sqrt(x^2 - 1)$,
    $"arctanh" (x)$, $1 / (1-x^2)$,
    $1 / f(x)$, $(- f' (x)) / ((f(x))^2)$,
    $a^(c x)$, $a^(c x) dot c ln (a)$,
    $x^x$, $x^x dot (1 + ln (x))_( x > 0)$,
    $(x^x)^x$, $(x^x)^x (x + 2 x ln (x))_(x > 0)$,
    $x^((x^x))$, $x^((x^x)) (&x^(x-1) + ln (x) dot &x^x (1 + ln (x))), space.quad x > 0$,
    $1 / a ln (a x + b)$, $1 / (a x + b)$,
    $(a x) / c - (a d - b c) / c^2 ln (| c x + d|)$, $(a x + b) / (c x + d)$,
    $1 / (2 a) ln (| (x - a) / (x + a)|)$, $1 / (x^2 - a^2)$,
    $x / 2 f(x) + a^2 / 2 ln (x + f(x))$, $sqrt(a^2 + x^2)$,
    $x / 2 sqrt(a^2 - x^2) - a^2 / 2 arcsin (x / (|a|))$, $sqrt(a^2 - x^2)$,
    $x / 2 f(x) - a^2 / 2 ln (x + f(x))$, $sqrt(x^2 - a^2)$,
    $ln(x + sqrt(x^2 plus.minus a^2))$, $1 / sqrt(x^2 plus.minus a^2)$,
    $arcsin (x / (|a|))$, $1 / sqrt(a^2 - x^2)$,
    $1 / a arctan (x / a)$, $1 / (x^2 + a^2)$,
    $- 1 / a cos (a x + b)$, $sin (a x + b)$,
    $1 / a sin (a x + b)$, $cos (a x + b)$,
    $- ln (|cos (x)|)$, $tan (x)$,
    $ln(|sin (x)|)$, $cot (x)$,
    $ln (| tan ( x / 2) |)$, $1 / (sin (x))$,
    $ln (| tan (x / 2 + pi / 4) | )$, $1 / (cos (x))$,
    $1 / 2 (x - sin (x) cos (x))$, $sin^2 (x)$,
    $1 / 12 (cos (3 x) - 9 cos (x))$, $sin^3 (x)$,
    $1 / 32 (12 x - 8 sin (2 x) + sin (4 x))$, $sin^4 (x)$,
    $1 / 2 (x + sin (x) cos (x))$, $cos^2 (x)$,
    $1 / 12 (9 sin (x) + sin (3 x))$, $cos^3 (x)$,
    $1 / 32 (12 x + 8 sin (2 x) + sin (4 x))$, $cos^4 (x)$,
    $tan (x)- x$, $tan^2 (x)$,
    $- cot (x) - x$, $cot^2 (x)$,
    $x arcsin (x) + sqrt(1 - x^2)$, $arcsin (x)$,
    $x arccos (x) - sqrt(1 - x^2)$, $arccos (x)$,
    $x arctan (x) - 1 / 2 ln (1 + x^2)$, $arctan (x)$,
    $ln (cosh (x))$, $tanh (x)$,
    $ln ( |f (x)|)$, $(f'(x)) / (f(x))$,
    $x dot (ln (|x|) -1)$, $ln (|x|)$,
    $1 / (n+1) (ln (x))^(n+1)_(n != -1)$, $1 / x (ln (x))^n$,
    $1 / (2n) (ln (x^n))^2_(n != 0)$, $1 / x ln (x^n)$,
    $ln (|ln (x) |)_(x > 0, x != 1)$, $1 / (x ln(x))$,
    $1 / (b ln(a)) a^(b x)$, $a^(b x)$,
    $(c x - 1) / (c^2) dot e^(c x)$, $x dot e^(c x)$,
    $(x^(n + 1)) / (n + 1) (ln (x) - 1 / (n + 1))_(n != -1)$, $x^n ln(x)$,
    $(e^(c x) (c sin (a x + b) - a cos (a x + b))) / (a^2 + c^2)$, $e^(c x) sin (a x + b)$,
    $(e^(c x) (c cos (a x + b) + a sin (a x + b))) / (a^2 + c^2)$, $e^(c x) cos ( a x + b)$,
    $(sin^(n+1) (x)) / (n+1)$, $sin^n (x) cos (x)$,
    $- (cos^(n+1) (x)) / (n+1)$, $sin (x) cos^n (x)$,
    $(4 x - sin (4 x)) / 32$, $sin^2 (x) cos^2 (x)$,
    $(cos ( 6 x) - 9 cos (2 x)) / 192$, $sin^3 (x) cos^3 (x)$,
    $(cos^3 (x) (3 cos (2 x) - 7)) / 30$, $sin^3 (x) cos^2 (x)$,
    $(sin^3 (x) (3 sin (2 x) - 7)) / 30$, $sin^2 (x) cos^3 (x)$,
  )
]

=== Binomial Formulas

#form()[
  $
    (a + b)^2 &= a^2 + 2 a b + b^2 \
    (a - b)^2 &= a^2 - 2 a b + b^2 \
    (a + b) (a - b) &= a^2 - b^2
  $
]

==== Pascal's Triangle

// i wanted to do something fun. this was very fun indeed
#form()[
  #align(
    center,
    {
      let r = 0
      while r <= 6 {
        let c = 0
        while (c <= r) {
          [$#calc.binom(r, c) space.quad$]
          c += 1
        }
        [ \ ]
        r += 1
      }
    },
  )
]

=== Bijection, Injection and Surjection

#form()[
  / Injective: Every $x$ as a unique $y$
  / Surjective: Every $y$ has a unique $x$
  / Bijective: Injective and Surjective
]

=== Binomial Coefficient

#form()[
  $ vec(n, k) = (n!) / (k! (n - k)!) $
]

=== Constants

#form()[
  $
    pi &= #calc.pi \
    e &= #calc.e \
    c &= 299792458 m / s
  $
]

=== Partial Integration

#form()[
  Let $a lt b$ be real numbers and $f, g: [a, b] arrow.r RR$ be continuously differentiable. Then the following holds:

  $
    integral_a^b (f dot g') d x &= f dot g bar_a^b - integral_a^b (f' dot g) d x
  $

  For indefinite integrals:
  $
    integral (f dot g') d x &= f dot g - integral (f' dot g) d x
  $

  Useful if arc- or log-functions appear, $x^n$, $1 / (1 - x^2)$, $1 / (1 + x^2)$, $dots$

]

=== Substitution

#form()[
  Substitution is the inverse of the chain rule and is particularly useful when working with composite functions.

  Let $a lt b$, $phi : [a, b] arrow.r RR$ be continuously differentiable, $I subset.eq RR$ an interval such that $phi ([a, b]) subset.eq I$, and $f : I arrow.r RR$ a continuous function. Then the following holds:
  $
    integral_a^b f (phi (t)) dot phi'(t) d t &= integral_(phi (a))^(phi (b)) f (x) d x
  $

  For indefinite integrals:
  $
    integral f (phi (t)) dot phi'(t) d t &= integral f (x) d x
  $

  Example:
  $
    integral x / sqrt(9 - x^2) d x " substitute " t = sqrt(9 - x^2)
  $

  1. Rewrite:
  $
    x = sqrt(9 - t^2) arrow.r.double x' = (-2t) / (2 sqrt(9 - t^2)) arrow.r.double d x = (-t dot d t) / sqrt(9 - t^2)
  $

  2. Substitution simplifies the integral:
  $
    integral - d t = -t " back substitution " arrow.r.double -sqrt(9 - x^2)
  $
]

#show math.equation: set block(breakable: false)

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
    inset: (x: 5pt, y: 6pt),
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
    [$m$: Freedom Degree],
    [$m$],
    [$2m$],
    [$1 / (2^(m / 2) Gamma (m / 2)) t^(m / 2 - 1) e^(- t / 2) "for" t >= 0$],
    [$P(m / 2, t / 2)$],
    [goodness-of-fit, independence test, hypothesis testing],

    [Student's $t$],
    [$t_m$],
    [$m$: Freedom Degree],
    [$cases(0 space.quad &m > 1, "undef." space.quad &"otherwise")$],
    [$cases(m / (m-2) space.quad &m > 2, infinity space.quad &1 < m <= 2, "undef." space.quad &"otherwise")$],
    [$(Gamma ((m+1) / 2)) / (sqrt(m pi) Gamma (m / 2)) (1 + (t^2) / m)^(- (m+1) / 2)$],
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
