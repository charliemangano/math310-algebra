#set document(
	author: "charlie mangano",
	date: auto,
	title: [algebra summary],
)
#set page(
    paper: "iso-b5",
    header: [
        _charlie mangano_ #h(1fr) #emph([#datetime.today().display("[day].[month].[year]")])
    ],
    numbering: "1",
)
#set heading(
    numbering: "I. i. ",
)
#let remark(body) = {
    pad(
        x: 1em,
        [*:: remark ::* #body]
    )
}
#let item(item_type, name : "", body) = {
	let snd_separator = if name == "" { "" } else { " :: " }
	[*#item_type ::* #emph([#name])*#snd_separator* #body]
}

#align(
    center, 
    text(2.2em)[
      *algebra :: summary* \
    ]
)

= integers.
== well ordering principle. prime factorization.

#item("def", name : "natural numbers", [$ NN = {0, 1, 2,...} $])
#item("def", name : "a divides b", [with $a, b in ZZ$ and $a != 0$, $ exists c in ZZ : b = a c "  (notation: " a|b ")" $])
#item("def", name : "prime", [$p in ZZ^+$, $ p > 1 and "only" {1, p}|p $])
#item("axiom", name : "well-ordering", [$forall S subset.eq NN without {emptyset}$, $ exists s in S : forall n in NN, s <= n "  (least element)" $])
#item("axiom", name : "induction", [$S subset NN$, $ [0 in S and n in S => n + 1 in S] $ $ => S = NN $])
#item("th", name : "fund. th. or arithmetic", [any integer greater than 1 is a product of primes, and its prime factorization is unique])

== euclidean division. bezout's identity.
#item("def", name : "gcd", [$a,b,d,e in ZZ^*$, $ d|{a,b} and [e|{a,b} => e|d] "  (notation: "d = gcd(a,b)")" $])
#item("def", name : "lcm", [$a,b,l,m in ZZ^*$, $ {a,b}|l and [{a,b}|m => l|m] "  (notation: "l = "lcm"(a,b)")" $])
#item("def", name : "euler's totient", [$a,n in NN$, $ P = {a in [|1,n|] : gcd(a,n) = 1} subset NN $ $ => phi(n) = |P| "  (notation : "phi(dot)")" $])
#remark([$gcd(n,m) = 1 => phi(n m) = phi(n) phi(m)$])
#item("th", name : "euclidean division", [$n in ZZ, d in ZZ^+$, $ exists! q,r in ZZ : n = q d + r, " with" r in [|0, d-1|] $])
#item("lem", [$n,q in ZZ, d in ZZ^+$, $ n = q d + r => gcd(n,d) = gcd(d,r) $])
#item("corr", [$forall a,b in ZZ^*$, $ exists x,y in ZZ : gcd(a,b) = a x + b y $])
#item("corr", [$a,b in ZZ^*$ and $d = gcd(a,b)$ $ a x + b y = c, c in ZZ^* "has integer solution" <=> c in d ZZ $])
#remark([_bezout's identity_ :: with $d = 1$ we have: $" "exists x,y in ZZ : a x + b y = 1$])


= groups.
== definitions.
#item("def", name : "group", [set $G$ with a binary operation $" "dot : G times G -> G " "$ with: $ (a dot b) dot c = a dot (b dot c) "  (associativity)" $ $ exists e in G : forall a in G, e dot a = a dot e = a "  (identity)" $ $ forall a in G, exists a^(-1) in G : a dot a^(-1) = a^(-1) dot a = e "  (inverse)" $])
#item("def", name : "finite", [$ (G, dot) "finite" <=> G "finite" $])
#item("def", name : "abelian", [$forall a,b in G$, $ a dot b = b dot a "  (commutative)" $])
#item("def", name : "order of group", [$ "order of" (G, dot) = |G| "  (notation: "|G|")" $])
#item("def", name : "generators", [$(G. dot)$ and $S subset G$, $ forall g in G, exists s_1 dots s_k in S : g = product s_i $])
#item("def", name : [relation in $G$], [any equation $R : G -> G$ satisfied by all of $G$'s generators \ ])
#item("def", name : [presentation in $S$'s and $R$'s], [set $S subset G$ of generators of $G$ and $R_i$ the minimal set of relations, $ angle.l S | R_1 dots R_k angle.r $])
#item("def", name : "order of element", [$g in G$, $ "smallest" n in NN : g^n = e "  (notation: "o(g)")" $])
#remark([$exists.not n in NN : n = o(g) => o(g) = infinity and G "infinite"$])
#item("def", name : "cyclic group", [$|G| = k$ $ exists g in G : G = {e, g, g^2, dots, g^(k-1)} $])

== group homomorphisms. subgroups. normal subgroups.
#item("def", name : "homomorphisms", [$phi.alt : G -> H$, with $(G, dot_G)$ and $(H, dot_H)$, $ forall x,y in G, phi.alt(x dot_G y) = phi.alt(x) dot_H phi.alt(y) $])
#remark([_isomorphism_ :: bijective homomorphism $phi.alt : G -> H$])
#remark([_endomorphism_ :: bijective homomorphism $phi.alt : G -> G$])
#item("def", name : "kernel, image", [$phi.alt : G -> H$ $ ker(phi.alt) = {g in G : phi.alt(g) = e_H} $ $ im(phi.alt) = {h in H : exists g in G : phi.alt(g) = h} $])
#remark([to check if $phi.alt : G -> H$ is a homomorphism, check that $phi.alt(s_G) in H$ satisfy $R_G_i$, with $s_G in S subset G$ and $R_G_i$ relations in $G$])
#item("def", name : "subgroup", [$H subset G, H != {emptyset} : (H, dot_G)$ is a group, $ e_G in H "  (identity)" $ $ forall a,b in H, a dot_G b in H "  (stable wrt "dot_G")" $])
#remark([$phi.alt : G -> H "homomorphism" => im(phi.alt) subset H$ (subgroup)])
#item("def", name : "normal subgroup", [$forall g in G, forall h in H$, $ g h g^(-1) in H "  (notation: "H lt.tri G")" $])
#remark([$G "abelian" => forall H subset G, H lt.tri G$])
#remark([$phi.alt : G -> H "homomorphism" => ker(phi.alt) lt.tri G$])

== dihedral group.
#item("def", name : "dihedral group", [symmetries of a regular $n$-gon with composition operation $compose$. $forall n >= 3,$ $ D_n = angle.l r,s | r^n = e, s^2 = e, s r s = r^(-1) angle.r $])
#remark([$D_n$ is non-abelian])
#remark([$|D_n| = 2n$])

== cosets. lagrange's theorem.
#item("def", name : [left coset wrt $H$ in $G$], [subgroup $H subset G$ and $g in G$, $ g H = {g h, h in H} subset G $])
#remark([$H$-cosets form a partition of $G$])
#remark([$H "finite" => forall x,y in G |x H| = |y H|$])
#item("th", name : "lagrange's", [$"subgroup" H subset G$ with $G$ finite, $ exists k in NN : |G| = k|H| $])
#remark([_index of $H$ in $G$_ :: $[G:H] := k = (|G|)/(|H|)$])
#item("corr", [$G$ finite, $ forall g in G, exists k in NN : |G| = k o(g) $])
#item("corr", [$G$ finite and $g in G$, $ g^(|G|) = e $])
#item("corr", [$G$ finite, $ |G| = p "prime" => G "cyclic" $])

== applications of lagrange's theorem.
#item("def", name : [group of units in $ZZ"/"n ZZ$], [$(ZZ"/"n ZZ, dot)$, $ ((ZZ"/"n ZZ)^*, dot) = {x in ZZ"/"n ZZ : exists x^(-1) in ZZ"/"n ZZ} "  (invertible)" $])
#remark([$[a]_n in ZZ"/"n ZZ, [a]_n != [0]_n$, $ [a]_n "unit in" ZZ"/"n ZZ <=> gcd(a,n) = 1 $ $ |(ZZ"/"n ZZ)^*, dot| = phi(n) $])
#remark([$p in ZZ "prime" => (ZZ"/"n ZZ)^*, dot) "cyclic" and |(ZZ"/"n ZZ)^*, dot)| = p - 1$])
#item("th", name : "fermat's little", [$p in NN$ prime and $z in ZZ$, $ p divides.not a => a^(p-1) equiv 1 " " (mod p) $])
#item("th", name : "euler's", [$a,n in ZZ^+$, $ gcd(a,n) = 1 => a^(phi(n)) = 1 " " (mod n) $])

== quotient group.
#item("def", name : "quotient group", [$G$ and $N lt.tri G$, $ G"/"N = {(x N), forall x in G} "  (left N-cosets)" $ $ "with operation" (x N) dot_(G"/"N) (y N) = (x y N) $ $ e_(G"/"N) = 1N "and" (x N)^(-1) = x^(-1) N $])
#remark([$phi.alt : G -> H$ homomorphism, $ G"/"ker(phi.alt) tilde.equiv im(phi.alt)$])

== symmetric group.
#item("def", name : "G acts on E", [$(G, dot_G)$ finite group and $E$ finite set, $ exists dot : G times E -> E " with" $ $ forall x in E, e_G dot x = x in E "  (identity)" $ $ forall g_1,g_2 in G, forall x in E, (g_1 dot g_2) dot x = g_1 dot (g_2 dot x) "  (associativity)" $])
#item("def", name : "orbit", [$G$ acts on $E$ with operation $dot$, $forall x in E$, $ "orb"(x) = {g dot x, g in G} $])
#remark([$|"orb"(x)| = 1 => x "\"fixed point\"" $])
#remark([$E = union_i "orb"(x_i) and "orb"_i union "orb"_j = emptyset$])
#item("def", name : "symmetric group", [$n in NN, n >= 1$ $ S_n =(rho, dot_S_n) " with" $ $ rho : {1, dots n} -> {1, dots n} "injective  (permutations)" $ $ e_S_n = rho : rho(i) = i and rho^(-1) : rho^(-1)(rho(i)) = i $])
#remark([the symmetric group of order $n$ is the group of $rho$'s of order $n$, and $|S_n| = n!$ is the order of the group itself])
#item("def", name : "k-cycle", [$sigma in S_n$ permutation and $angle.l sigma angle.r subset S_n$ subgroup generated by $sigma$, $ exists ! i in {1 dots n} : |"orb"_sigma (i)| "non-trivial" in {sigma(i)}_(i in {1 dots n}) \ => sigma " "k"-cycle with" k := |"orb"_sigma (i)| $])
#remark([_transposition_ :: 2-cycle])
#remark([_cycle notation_ :: $pi in S_n$ a $k$-cycle and $x in {1 dots n}$ in the non-trivial orbit of $pi$, $pi = (x" "pi(x)" "pi^2(x)" "dots" "pi^(k-1)(x))$ the cycle notation of $pi$])
#item("def", name : "disjoint cycles", [$pi_1, pi_2 in S_n$ $k$-cycles are disjoint if their non-trivial orbits don't intersect])
#remark([disjoint cycles commute in $S_n$])
#item("def", name : "odd/even permutation", [$pi in S_n$ permutation and $rho_i in S_n$ transpositions ,$ pi = rho_1 dot rho_2 dot dots dot rho_r " " cases("even if" r "even", "odd if" r "odd") $])
#item("th", [a permutation is a unique product of disjoint cycles, up to the order of factors])
#remark([every $k$-cycle in $S_n$ is a product of $k-1$ transposition not necessarily disjoint])
#remark([$(1" "2" "dots" "k) = (1" "k)(1" "k-1) dots (1" "3)(1" "2)$])
#remark([_cycle decomposition_ :: $pi,rho in S_n$, the cycle decomposition of $pi rho pi^(-1)$ is obtained by replacing every $i$ in the cycle decomposition of $rho$ by $pi(i)$])
#item("corr", [$S_n$ is generated by ${(i j)}_(1 <= i < j <= n)$])
#item("prop", [$A_n subset S_n$, $ A_n = {rho "even"} => A_n lt.tri S_n and [S_n : A_n] = 2 $])

== orbit-stabilizer theorem.
#item("def", name : "stabilizer", [$G$ acting on $E$, $forall x in E$, $ "stab"(x) = {g in G : g dot x = x} $])
#remark([$"stab"(x), x in E$ is a subgroup of $G$])
#item("th", name : "orbit-stabilizer", [$G$ acting on $E$ and $forall x in E$, $ |"orb"(x)| = [G : "stab"(x)] $])

== conjugacy classes. class equation.
#item("def", name : "cycle type", [$sigma in S_n$ and $sigma = sigma_1 dots sigma_r$ disjoint cycle decomposition, $ {l in NN : l_i = "length"(sigma_i), 1<=i<=r} $])
#item("def", name : "conjugacy class in G", [$forall x,g in G $, $ g dot x = g x g^(-1) "(acts on itself by conjugation)" \ => C_x := "orb"(x) $])
#remark([$g_1, g_2 in S_n, "cycle type"_1 = "cycle type"_2 <=> C^(S_n)_(g_1)= C^(S_n)_(g_2) $])
#remark([$forall x in S_n, exists "bijection" C^(S_n)_x -> "cycle type"_x$])
#item("def", name : "centralizer", [$forall x,g in G $, $ g dot x = g x g^(-1) "(acts on itself by conjugation)" \ => G_x := "stab"(x) subset G $])
#item("def", name : "center", [$ Z(G) = {x in G : forall g in G, x dot g = g dot x } $])
#item("th", name : "class equation", [$G$ finite and ${x_i}^m_(i=1)$ set of representatives of the ${C_x_i}^m_(i=1)$ containing more than one element, $ |G| &= |Z(G)| + sum^m_(i=1)|C_x_1| \ &= |Z(G)| + sum^m_(i=1)[G:G_x_i] $])

== direct product of groups.
#item("def", name : "direct product", [$G, H$ groups, $G times H$ a group with: $ G times H = {(g,h) : g in G, h in H} "with" \ forall g_1,g_2 in G, forall h_1,h_2 in H, (g_1, h_1) dot_(G times H) (g_2, h_2) = (g_1 dot_G g_2, h_1 dot_H h_2) \ e_(G times H) = (e_G, e_H) and (g,h)^(-1) = (g^(-1),h^(-1)) $])
#remark([$G times H tilde.equiv H times G$])
#remark([$G times H "abelian" <=> G "abelian" and H "abelian"$])
#remark([${(e_G,h), h in H} cases(subset G times H "subgroup", tilde.equiv H)$ and ${(g,e_H), g in G} cases(subset G times H "subgroup", tilde.equiv G)$])
#remark([for cyclic groups, $C_n times C_m tilde.equiv C_(n m) <=> gcd(n,m) = 1$])
#set math.cases(reverse: true)
#remark([$H,K subset G$ subgroups, $cases(H sect K = {e_G} \ forall h in H\, forall k in K\, h k = k h \ {h k, h in H, k in K} "span" G) => G tilde.equiv H times K$])
#set math.cases(reverse: false)

== classification of finite abelian groups.
#item("def", name : "simple group", [$ exists.not H subset G "subgroup" : H != {e_G} "(non trivial)" and H != G ("not proper") $])
#item("th", name : "cauchy's", [$G$ finite abelian, $ p in NN "prime" : p|"order of" G => exists g in G : o(g) = p $])
#item("corr", [$G$ finite abelian, $ exists p in NN, p "prime" : G tilde.equiv C_p  $])
#item("def", name : "partition of n", [$n in NN$, $ {m_i in NN, m_i >= 1 : m_1 + dots m_k = n} $])
#item("prop", [$G$ abelian, $n in NN$ and $p$ prime, $ |G| = p^n => exists! {m_i in NN}_(1 <= i <= k <= n) "partition of "n : G tilde.equiv C_(p^(m_1)) times dots times C_(p^(m_k)) $])
#remark([different partitions of $n$ correspond to non-isomorphic abelian groups])
#item("prop", [$G$ finite abelian and $p_1 dots p_r$ distinct primes, $ |G| = p^(n_1)_1 dots p^(n_r)_r => G tilde.equiv G_(p_1^(n_1)) times dots times G_(p_r^(n_r)) $])
#item("th", name : "classification finite abelian groups", [$G$ finite abelian and $p_1 dots p_r$ not necessarily distinct primes, $ G tilde.equiv C_(p_1^(alpha_1)) times dots times C_(p_m^(alpha_m)) "with" |G| = p^(alpha_1)_1 dots p^(alpha_m)_m $])
#remark([_elementary divisors_ :: the $m$-tuples $(p^(alpha_1)_1, dots , p^(alpha_m)_m)$ are elementary divisors of $G$])
#item("th", [$G$ finite abelian and $|G| = d_1 dots d_k$ , $ d_k|d_(k-1) and dots and d_2|d_1 =>  G tilde.equiv C_d_1 times dots times C_d_k $])
#remark([_invariant factors_ :: the $k$-tuples $(d_k, dots , d_1)$ are the invariant factors of $G$])

