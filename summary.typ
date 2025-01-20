#set document(
	author: "charlie mangano",
	date: auto,
	title: [algebra summary],
)
#set page(
	header: [
		_charlie mangano_ #h(1fr) _18.02.2024_
	],
	numbering: "1",
)
#set heading(
	numbering: "I. i. ",
)
#let remark(body) = {
	pad(
		x: 2em,
		[*:: remark ::* #body]
	)
}


#align(
	center, 
	text(2.5em)[
  	*algebra :: summary* \
	]
)


= integers.

== well ordering principle. prime factorization.

*def ::* _natural numbers_ :: $ NN = {0, 1, 2,...} $ 
*def ::* _a divides b_ :: with $a, b in ZZ$ and $a != 0$, $ exists c in ZZ : b = a c "  (notation: " a|b ")" $ 
*def ::* _prime_ :: $p in ZZ^+$, $ p > 1 and "only" {1, p}|p $
*axiom:* _well-ordering_ :: $forall S subset.eq NN without {emptyset}$, $ exists s in S : forall n in NN, s <= n "  (least element)" $
*axiom ::* _induction_ :: $S subset NN$, $ [0 in S and n in S => n + 1 in S] $ $ => S = NN $
*th ::* _fund. th. or arithmetic_ :: any integer greater than 1 is a product of primes, and its prime factorization is unique

== euclidean division. bezout's identity.
*def ::* _gcd_ :: $a,b,d,e in ZZ^*$, $ d|{a,b} and [e|{a,b} => e|d] "  (notation: "d = gcd(a,b)")" $
*def ::* _lcm_ :: $a,b,l,m in ZZ^*$, $ {a,b}|l and [{a,b}|m => l|m] "  (notation: "l = "lcm"(a,b)")" $
*def ::* _euler's totient_ :: $a,n in NN$, $ P = {a in [|1,n|] : gcd(a,n) = 1} subset NN $ $ => phi(n) = |P| "  (notation : "phi(dot)")" $ #remark($gcd(n,m) = 1 => phi(n m) = phi(n) phi(m)$)
*th ::* _euclidean division_ :: $n in ZZ, d in ZZ^+$, $ exists! q,r in ZZ : n = q d + r, " with" r in [|0, d-1|] $
*lem ::* $n,q in ZZ, d in ZZ^+$, $ n = q d + r => gcd(n,d) = gcd(d,r) $
*corr ::* $forall a,b in ZZ^*$, $ exists x,y in ZZ : gcd(a,b) = a x + b y $
*corr ::* $a,b in ZZ^*$ and $d = gcd(a,b)$ $ a x + b y = c, c in ZZ^* "has integer solution" <=> c in d ZZ $ #remark([_bezout's identity_ :: with $d = 1$ we have: $" "exists x,y in ZZ : a x + b y = 1$])


= groups.

== definitions.
*def ::* _group_ :: set $G$ with a binary operation $" "dot : G times G -> G " "$ with: $ (a dot b) dot c = a dot (b dot c) "  (associativity)" $ $ exists e in G : forall a in G, e dot a = a dot e = a "  (identity)" $ $ forall a in G, exists a^(-1) in G : a dot a^(-1) = a^(-1) = e "  (inverse)" $
*def ::* _finite_ :: $ (G, dot) "finite" <=> G "finite" $ 
*def ::* _abelian_ :: $forall a,b in G$, $ a dot b = b dot a "  (commutative)" $
*def ::* _order of group_ :: $ "order of" (G, dot) = |G| "  (notation: "|G|")" $
*def ::* _generators_ :: $(G. dot)$ and $S subset G$, $ forall g in G, exists s_1 dots s_k in S : g = product s_i $
*def ::* _relation in $G$_ :: any equation $R : G -> G$ satisfied by all of $G$'s generators \
*def ::* _presentation in $S$'s and $R$'s_ :: set $S subset G$ of generators of $G$ and $R_i$ the minimal set of relations, $ angle.l S | R_1 dots R_k angle.r $
*def ::* _order of element_ :: $g in G$, $ "smallest" n in NN : g^n = e "  (notation: "o(g)")" $ #remark($exists.not n in NN : n = o(g) => o(g) = infinity and G "infinite"$)
*def ::* _cyclic group_ :: $|G| = k$ $ exists g in G : G = {e, g, g^2, dots, g^(k-1)} $

== group homomorphisms. subgroups. normal subgroups.
*def ::* _homomorphisms_ :: $phi.alt : G -> H$, with $(G, dot_G)$ and $(H, dot_H)$, $ forall x,y in G, phi.alt(x dot_G y) = phi.alt(x) dot_H phi.alt(y) $ #remark([_isomorphism_ :: bijective homomorphism $phi.alt : G -> H$]) #remark([_endomorphism_ :: bijective homomorphism $phi.alt : G -> G$])
*def ::* _kernel, image_ :: $phi.alt : G -> H$ $ ker(phi.alt) = {g in G : phi.alt(g) = e_H} $ $ im(phi.alt) = {h in H : exists g in G : phi.alt(g) = h} $ #remark([to check if $phi.alt : G -> H$ is a homomorphism, check that $phi.alt(s_G) in H$ satisfy $R_G_i$, with $s_G in S subset G$ and $R_G_i$ relations in $G$])
*def ::* _subgroup_ :: $H subset G, H != {emptyset} : (H, dot_G)$ is a group, $ e_G in H "  (identity)" $ $ forall a,b in H, a dot_G b in H "  (stable wrt "dot_G")" $ #remark([$phi.alt : G -> H "homomorphism" => im(phi.alt) subset H$ (subgroup)])
*def ::* _normal subgroup_ :: $forall g in G, forall h in H$, $ g h g^(-1) in H "  (notation: "H lt.tri G")" $ #remark([$G "abelian" => forall H subset G, H lt.tri G$]) #remark([$phi.alt : G -> H "homomorphism" => ker(phi.alt) lt.tri G$])

== dihedral group.
*def ::* _dihedral group_ :: symmetries of a regular $n$-gon with composition operation $compose$. $forall n >= 3,$ $ D_n = angle.l r,s | r^n = e, s^2 = e, s r s = r^(-1) angle.r $ #remark([$D_n$ is non-abelian]) #remark([$|D_n| = 2n$])

== cosets. lagrange's theorem.
*def ::* _left coset wrt $H$ in $G$_ :: subgroup $H subset G$ and $g in G$, $ g H = {g h, h in H} subset G $ #remark([$H$-cosets form a partition of $G$]) #remark([$H "finite" => forall x,y in G |x H| = |y H|$])
*th ::* _lagrange's_ :: $"subgroup" H subset G$ with $G$ finite, $ exists k in NN : |G| = k|H| $ #remark([_index of $H$ in $G$_ :: $[G:H] := k = (|G|)/(|H|)$]) 
*corr ::* $G$ finite, $ forall g in G, exists k in NN : |G| = k o(g) $
*corr ::* $G$ finite and $g in G$, $ g^(|G|) = e $ 
*corr ::* $G$ finite, $ |G| = p "prime" => G "cyclic" $

== applications of lagrange's theorem.
*def ::* _group of units in $ZZ"/"n ZZ$_ :: $(ZZ"/"n ZZ, dot)$, $ ((ZZ"/"n ZZ)^*, dot) = {x in ZZ"/"n ZZ : exists x^(-1) in ZZ"/"n ZZ} "  (invertible)" $ #remark([$[a]_n in ZZ"/"n ZZ, [a]_n != [0]_n$, $ [a]_n "unit in" ZZ"/"n ZZ <=> gcd(a,n) = 1 $ $ |(ZZ"/"n ZZ)^*, dot| = phi(n) $ ]) 
**

== quotient group.

== symmetric group.

== orbit-stabilizer theorem.

== conjugacy classes. class equation.

== direct product of groups.

== classification of finite abelian groups.



