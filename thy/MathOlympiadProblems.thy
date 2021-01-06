theory MathOlympiadProblems
imports Complex_Main Dirichlet_Series.Arithmetic_Summatory Dirichlet_Series.Divisor_Count 
begin

section \<open>India 2014 Question 2\<close>

(*
https://www.youtube.com/watch?v=SEHhzkH3ZqM
https://en.wikipedia.org/wiki/Floor_and_ceiling_functions#Equivalences
https://www.youtube.com/watch?v=KMyQIPc4pgA&feature=youtu.be
https://math.stackexchange.com/questions/338432/how-to-prove-the-relation-between-the-floor-function-and-the-number-of-divisors
*)

sledgehammer_params[debug=true,timeout=600]

abbreviation divisors :: "nat \<Rightarrow> int" where
  "divisors n \<equiv> card { d. d dvd n }"

abbreviation psq where
  "psq n \<equiv> (\<exists>a. n = a\<^sup>2)"

lemma not_psq:
  fixes n::nat
  assumes "\<not> (psq n)"
  shows "\<forall>a::nat. n \<noteq> a\<^sup>2"  using assms by simp

(* Proof borrowed from sum_upto_sum_divisors; seems easier than trying to fit proof to use sum_upto_sum_divisors *)
lemma sum_div_sum_divisors:
  fixes n::nat
  shows  "(\<Sum>k \<in> {1..n}.  \<lfloor>n / k \<rfloor>) = (\<Sum>i \<in> {1..n}. divisors(i))" 
proof - 
  let ?A = "SIGMA  i: {1..n}. {d. d dvd i}"
  let ?B = "SIGMA  k: {1..n}. {1.. nat \<lfloor>n / k \<rfloor> }"

  have bij: "bij_betw (\<lambda>(k,d). (d * k, k)) ?B ?A"
    apply(rule bij_betwI[where g = "\<lambda>(k,d). (d, k div d)"],auto+ )
    apply(metis floor_divide_of_nat_eq le_trans mult.commute mult_le_mono2 nat_int times_div_less_eq_dividend)
     apply(meson Suc_le_lessD dvd_imp_le le_trans)
  by (simp add: div_le_mono floor_divide_of_nat_eq)

  
  have "(\<Sum>i \<in> {1..n}. divisors(i)) = (\<Sum>(k,d)\<in>?A. 1)" 
    using sum.Sigma[of "{1..n}" "\<lambda>i. {d. d dvd i}"  "\<lambda>_ _. 1"] by simp
  also have "... = (\<Sum>(k,d)\<in>?B. 1)"   by (subst sum.reindex_bij_betw[OF bij, symmetric]) (auto simp: case_prod_unfold)
  also have "... = (\<Sum>k \<in> {1..n}.  \<lfloor>real n / real k \<rfloor>)" using
   sum.Sigma[of "{1..n}" "\<lambda>k. {1.. nat \<lfloor>real n / real k \<rfloor> }" "\<lambda>_ _.1" ] by simp
  finally show ?thesis by auto
qed


(* From ME *)
lemma bij_betw_submultisets:
  "card {B. B \<subseteq># A} = (\<Prod>x\<in>set_mset A. count A x + 1)"
proof -
  define f :: "'a multiset \<Rightarrow> 'a \<Rightarrow> nat"
    where "f = (\<lambda>B x. if x \<in># A then count B x else undefined)"
  define g :: "('a \<Rightarrow> nat) \<Rightarrow> 'a multiset"
    where "g = (\<lambda>h. Abs_multiset (\<lambda>x. if x \<in># A then h x else 0))"

  have count_g: "count (g h) x = (if x \<in># A then h x else 0)"
    if "h \<in> (\<Pi>\<^sub>E x\<in>set_mset A. {0..count A x})" for h x
  proof -
    have "finite {x. (if x \<in># A then h x else 0) > 0}"
      by (rule finite_subset[of _ "set_mset A"]) (use that in auto)
    thus ?thesis by (simp add: multiset_def g_def)
  qed

  have f: "f B \<in> (\<Pi>\<^sub>E x\<in>set_mset A. {0..count A x})" if "B \<subseteq># A" for B
      using that by (auto simp: f_def subseteq_mset_def)

  have "bij_betw f {B. B \<subseteq># A} (\<Pi>\<^sub>E x\<in>set_mset A. {0..count A x})"
  proof (rule bij_betwI[where g = g], goal_cases)
    case 1
    thus ?case using f by auto
  next
    case 2
    show ?case
      by (auto simp: Pi_def PiE_def count_g subseteq_mset_def)
  next
    case (3 B)
    have "count (g (f B)) x  = count B x" for x
    proof -
      have "count (g (f B)) x = (if x \<in># A then f B x else 0)"
        using f 3 by (simp add: count_g)
      also have "\<dots> = count B x"
        using 3 by (auto simp: f_def dest: mset_subset_eqD)
      finally show ?thesis .
    qed
    thus ?case
      by (auto simp: multiset_eq_iff)
  next
    case 4
    thus ?case
      by (auto simp: fun_eq_iff f_def count_g)
  qed
  hence "card {B. B \<subseteq># A} = card (\<Pi>\<^sub>E x\<in>set_mset A. {0..count A x})"
    using bij_betw_same_card by blast
  thm card_PiE
  thus ?thesis
    by (simp add: card_PiE)
qed

lemma count_multiplicity:
  fixes n::nat
  assumes  "p \<in> prime_factors n"
  shows "count (prime_factorization n) p = multiplicity p n"
  using assms  count_prime_factorization_prime by blast

lemma num_divisors:
  fixes n :: nat
  assumes "n \<noteq> 0"
  shows  "card { d. d dvd n } = (\<Prod>p\<in> prime_factors n.  multiplicity p n + 1)"
proof - 
  define f :: "nat multiset \<Rightarrow> nat" where "f = prod_mset"
  define g :: "nat \<Rightarrow> nat multiset" where "g = prime_factorization"

  have "bij_betw f  { B . B \<subseteq># prime_factorization n} { d. d dvd n }" 
  proof (rule bij_betwI[where g = g], goal_cases)
    case 1
    {
      fix x
      assume "x \<in> {B. B \<subseteq># prime_factorization n}" 
      hence "f x \<in> { d . d dvd n}" using prime_factorization_subset_iff_dvd 
        using assms f_def prod_mset_subset_imp_dvd by fastforce
    }
    then show ?case by simp
  next
    case 2
    {
      fix x
      assume "x \<in> { d . d dvd n}" 
      hence "g x \<in>  {B. B \<subseteq># prime_factorization n}" using prime_factorization_subset_iff_dvd 
        using assms f_def prod_mset_subset_imp_dvd 
        by (metis g_def mem_Collect_eq prime_factorization_0 subset_mset.bot.extremum)
    }
    then show ?case by simp 
  next
    case (3 x)
    hence "(\<And>p. p \<in># x \<Longrightarrow> prime p)"  using mset_subset_eqD by fastforce
    then show ?case using f_def g_def assms prime_factorization_prod_mset_primes[of x] normalize_nat_def by auto
  next
    case (4 y)
    then show ?case using f_def g_def assms prod_mset_prime_factorization normalize_nat_def by auto
  qed

  hence  "card { d. d dvd n } = card {B. B \<subseteq># prime_factorization n}" 
    using prime_factorization_subset_iff_dvd bij_betw_same_card by force
  moreover have "(\<Prod>x\<in>prime_factors n. count (prime_factorization n) x + 1) = (\<Prod>p\<in>prime_factors n. multiplicity p n + 1)"
    using count_multiplicity 
    by (metis (no_types, lifting) prod.cong)
  ultimately show ?thesis using bij_betw_submultisets[of "prime_factorization n"] by simp
qed

lemma even_psq:
  fixes n::nat
  assumes "B =  prime_factorization n" and
         "\<forall>p \<in>#  B.  even( count B p )" and "n \<noteq> 0"
  shows "psq n"
proof -

  define f where "f = (\<lambda>p. if p \<in># B then (count B p)  div 2 else 0)" 
  define A where "A = Abs_multiset f"

  have fm: "f  \<in> multiset" proof -
    have "finite {x. 0 < f x}" using f_def 
      by (metis finite_nat_set_iff_bounded finite_set_mset mem_Collect_eq nat_neq_iff)
    thus ?thesis using multiset_def by auto
  qed

  have "A + A = B" proof  -
    have "(\<forall>p. count (A + A) p = count B p)"  using A_def assms fm f_def Abs_multiset_inverse  dvd_div_eq_iff by fastforce     
    thus ?thesis  using  multiset_eq_iff[of "A + A" B] by simp
  qed

  obtain a::nat where a:"a = prod_mset A"  by simp
 
  have "(\<And>p. p \<in># A \<Longrightarrow> prime p)" 
  proof -
    fix p
    assume "p \<in> set_mset A"
    hence "count A p > 0" by auto
    hence "count B p > 0" using assms 
      by (metis \<open>A + A = B\<close> count_eq_zero_iff neq0_conv union_iff)
    thus  "prime p" using assms prime_factorization_def by auto
  qed
 
  hence a2:"A = prime_factorization a"
    using  prime_factorization_exists[of a] normalize_nat_def prime_factorization_unique prime_factorization_prod_mset_primes            
    by (simp add: prime_factorization_prod_mset_primes a)
  hence "a \<noteq> 0" using a 
    by (metis prime_factorization_0 prod_mset_empty zero_neq_one)
  hence "prime_factorization (a * a) = A + A" 
     using prime_factorization_mult \<open>a \<noteq> 0\<close> a2 by auto
  hence "prime_factorization (a * a) = prime_factorization n" using  \<open>A + A = B\<close> assms by auto
  hence "n = a\<^sup>2" using prime_factorization_unique[of "a*a" n] normalize_nat_def a2 a 
    a2 a assms power2_eq_square \<open>a \<noteq> 0\<close>
    by (metis id_apply mult_is_0)
  thus ?thesis by simp
qed

lemma psq_even:
  fixes n::nat
  assumes  "psq n" and "B =  prime_factorization n"
  shows "\<forall>p \<in># B.  even ( count B p)"
using assms proof(cases "n=0")
  case True
  then show ?thesis  by (simp add: assms(2))
next
  case False
 
  obtain a::nat where a: "n = a\<^sup>2" using assms by auto

  define A where "A = prime_factorization a" 
  have "a \<noteq> 0"  using a False by simp
  hence "A + A = B" using prime_factorization_mult[of a a] a assms 
    by (simp add: A_def power2_eq_square)

  hence "\<forall>p \<in># B. count B p = count A p + count A p" using count_union by auto
  thus ?thesis by simp
qed

lemma num_divisors2:
  fixes n::nat
  assumes "n \<noteq> 0" and "A = prime_factorization n"
  shows "card {d. d dvd n} = (\<Prod>p \<in> set_mset A. count A p  + 1)" 
proof -
  have "\<forall>p \<in> set_mset A. count A p + 1 = multiplicity p n + 1" using count_prime_factorization_prime 
    by (simp add: assms(2) count_multiplicity)
  hence *:"(\<Prod>p \<in> set_mset A. multiplicity p n + 1) =  (\<Prod>p \<in> set_mset A. count A p  + 1)" 
    using assms prime_factorsI by auto   
  hence "(\<Prod>p \<in> prime_factors n . multiplicity p n + 1) =  (\<Prod>p \<in> set_mset A. multiplicity p n + 1)" 
    unfolding  prod_mset_def 
    using assms(2) by auto
  thus ?thesis using num_divisors[of n] assms * by auto
qed


lemma odd_even:
  fixes A::"'a set" 
  assumes "finite A"
  shows "odd (\<Prod>p \<in> A. (f p  + 1)) = (\<forall>p \<in> A. even (f p ))"
using assms proof(induct A rule:finite_induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  hence "(\<Prod>p\<in>insert x F. (f p + 1)) = (\<Prod>p\<in>F. f p + 1) * (f x + 1)" 
    by (simp add: mult.commute)
  then show ?case using insert 
    by auto
qed

lemma psq_odd_card_divisors:
  fixes n::nat
  assumes "n \<noteq> 0"
  shows "psq n \<longleftrightarrow> odd (divisors n)"
proof -
  obtain A where A:"A =  prime_factorization n" by auto
  hence *:"finite (set_mset A)" 
    by simp
  hence "odd (divisors n) = (\<forall>p \<in># A.  even ( count A p))" using num_divisors2[OF assms A]  
         odd_even[OF *, where f="count A"] 
    by presburger
  thus ?thesis using psq_even even_psq assms A by metis
qed
 

lemma sum_divisors_eq_sum_psq:
  fixes n::nat
  shows  "(\<Sum>k \<in> {1..n}. divisors(k)) mod 2 = ((\<Sum>k \<in> {1..n}. if psq k then 1 else 0)) mod 2"
proof(induct n)
  case 0
  then show ?case by auto
next
  case (Suc m)
  have "Suc m \<noteq> 0" by auto
  hence *: "(if psq (Suc m) then 1 else 0) =  divisors (Suc m) mod 2" using psq_odd_card_divisors[of "Suc m"] 
    by (metis parity_cases) 

  have "sum divisors {1..Suc m} mod 2  = (sum divisors {1..m} + divisors (Suc m) ) mod 2" 
    by auto
  also have "... = (sum divisors {1..m} mod 2 + divisors (Suc m) mod 2 ) mod 2" by presburger
  also have "... = (((\<Sum>k = 1..m. if psq k then 1 else 0) mod 2) +  divisors (Suc m) mod 2 ) mod 2" 
    using Suc by argo
  also have "... = (((\<Sum>k = 1..m. if psq k then 1 else 0) mod 2) + (if psq (Suc m) then 1 else 0) mod 2) mod 2" 
    using * by presburger
   also have "... = (((\<Sum>k = 1..m. if psq k then 1 else 0) + (if psq (Suc m) then 1 else 0)) mod 2) mod 2"      
     by (simp add: mod_add_left_eq)
   also have "... =  (\<Sum>k = 1..Suc m. if psq k then 1 else 0) mod 2"
     by auto
  finally show ?case by auto
qed



lemma divsuc:
  fixes n::nat
  assumes "n \<noteq> 0" and "k dvd (n+1)" and "k \<noteq> 1"
  shows "\<not> (k dvd n)"
using assms proof(induct n)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then show ?case using dvd_def 
    by (metis One_nat_def dvd_1_iff_1 dvd_add_right_iff)
qed  


lemma suc_n_product:
  fixes k::nat and n::nat
  assumes "n+1 = k * x" 
  shows "n = k*(x-1) + (k-1)"
proof -
  have "k*(x-1) + (k-1) = k*x - k + (k - 1)" using assms 
    by (simp add: right_diff_distrib')
  also have "... = k*x - 1" 
    using Nat.add_diff_assoc Suc_diff_1 assms diff_is_0_eq' le_add2 le_numeral_extra
      less_numeral_extra(1) one_le_mult_iff ordered_cancel_comm_monoid_diff_class.diff_add 
    
    by (metis add_right_imp_eq calculation mult.right_neutral nat_less_le no_zero_divisors zero_less_diff)
  finally have "k*(x-1) + (k-1) = n" using assms by simp
  thus ?thesis by simp
qed

lemma div_suc_n_mod_n:
  fixes k::nat and n::nat
  assumes "(n+1) mod k = 0" and "k > 0" and "n > 0" 
  shows "n mod k = k-1" using assms 
  by (smt Suc_lessI add.right_neutral add_eq_0_iff_both_eq_0 diff_Suc_1 
         group_cancel.add2 mod_add_left_eq mod_less plus_1_eq_Suc unique_euclidean_semiring_numeral_class.pos_mod_bound zero_neq_one)

lemma div_suc_n_div_n:
  fixes k::nat and n::nat
  assumes "(n+1) div k = x" and "(n+1) mod k = 0"
  shows "n div k = x - 1"
proof - 
  have "n+1 = k * x" using assms 
    by auto
  hence "n = k*(x-1) + (k-1)" using assms suc_n_product[of n k x] by auto
  moreover have "n mod k = k-1" using assms div_suc_n_mod_n 
    by (metis \<open>n + 1 = k * x\<close> add_gr_0 calculation mod_mod_trivial nat_0_less_mult_iff not_gr_zero)
  ultimately show ?thesis using div_mult_mod_eq[of n k] 
    by (metis Nat.add_0_right \<open>n + 1 = k * x\<close> assms(1) diff_0_eq_0 div_mult_self4 mod_div_trivial mult_eq_0_iff)
qed



lemma divstep:
  fixes k::nat and n::nat
  assumes "n \<noteq> 0" and "k dvd (n+1)" and "k > 1"
  shows "\<lfloor>(n+1)/k\<rfloor> = \<lfloor>n/k\<rfloor> + 1"
proof -
  have "\<lfloor>(n+1)/k\<rfloor> = (n+1) div k" using assms by fastforce
  hence "n div k = \<lfloor>(n+1)/k\<rfloor> - 1" using assms div_suc_n_div_n[of n k] 
    using dvd_div_gt0 int_ops(6) by auto
  moreover have "\<lfloor>n/k\<rfloor> = n div k" using assms 
    by (simp add: floor_divide_of_nat_eq)
  ultimately show ?thesis using assms by simp
qed



lemma sqrt_suc_le_suc_sqrt:
 fixes n::nat 
 shows  "sqrt(n+1) \<le> sqrt(n) + 1"
proof -
  have "n + 1 \<le> n + 2*sqrt(n) + 1" by simp
  moreover have "n + 2*sqrt(n) + 1 = (sqrt(n) + 1)\<^sup>2" proof -
    have "(sqrt(n) + 1)\<^sup>2 = (sqrt(n) + 1) * (sqrt(n) + 1)" 
      by (simp add: power2_eq_square)
    also have "... = sqrt(n)*sqrt(n) + 2*sqrt(n) + 1" by argo
    finally show ?thesis by auto
  qed

  ultimately have "n + 1 \<le> (sqrt(n) + 1)\<^sup>2" by simp
  thus ?thesis 
    by (smt \<open>real n + 2 * sqrt (real n) + 1 = (sqrt (real n) + 1)\<^sup>2\<close> of_nat_0 of_nat_le_0_iff real_le_lsqrt sqrt_le_D)
qed


lemma sqrt_suc_le_suc_sqrt2:
  fixes n::nat
  shows "\<lfloor>sqrt (n+1)\<rfloor> - \<lfloor>sqrt n\<rfloor> \<le> 1"
  using sqrt_suc_le_suc_sqrt[of n] 
  by linarith


lemma psq_imp_sqrt_suc_suc:
  fixes n::nat
  assumes "psq (n+1)"
  shows "\<lfloor>sqrt (n+1)\<rfloor> = \<lfloor>sqrt n\<rfloor>+1" 
proof -
  obtain a::nat where a:"n+1=a\<^sup>2" using assms by auto
  hence "\<lfloor>sqrt (n+1)\<rfloor> = a" by auto
  have "a - \<lfloor>sqrt n\<rfloor> = 1" proof(rule ccontr)
    assume "a - \<lfloor>sqrt n\<rfloor> \<noteq> 1"
    hence "\<lfloor>sqrt n\<rfloor> = a" using sqrt_suc_le_suc_sqrt2
      by (smt \<open>\<lfloor>sqrt (real (n + 1))\<rfloor> = int a\<close> floor_mono of_nat_1 of_nat_add real_sqrt_le_iff)
    hence "sqrt n \<ge> a" by linarith
    hence "n \<ge> a\<^sup>2" 
      using  a le_add2 of_nat_1 of_nat_add of_nat_le_of_nat_power_cancel_iff one_power2 power2_nat_le_eq_le real_le_lsqrt real_sqrt_eq_iff real_sqrt_unique      
      by (metis of_nat_0_le_iff power_mono real_sqrt_pow2_iff)
    thus False using a by simp
  qed
  thus ?thesis using a by simp
qed

lemma not_psq_imp_sqrt_suc_eq:
  fixes n::nat
  assumes "\<not> psq (n+1)"
  shows "\<lfloor>sqrt (n+1)\<rfloor> = \<lfloor>sqrt n\<rfloor>" 
proof -
  have psq: "\<forall>a::nat. n+1 \<noteq> a\<^sup>2" using assms not_psq[of "n+1"] by auto
  obtain a::nat where a_def:" a = \<lfloor>sqrt (n+1)\<rfloor>" 
    using nat_0_le of_nat_0_le_iff real_sqrt_ge_0_iff zero_le_floor by blast
  have 2:"n+1 < (a+1)\<^sup>2" proof(rule ccontr)
    assume "\<not> n + 1 < (a + 1)\<^sup>2" 
    hence "n+1 \<ge> (a + 1)\<^sup>2" by auto
    hence "sqrt (n+1) \<ge> a + 1" 
      using of_nat_le_of_nat_power_cancel_iff real_le_rsqrt by blast
    thus False using a_def by linarith
  qed
  moreover have 1:"a\<^sup>2 \<le> n" proof(rule ccontr)
    assume "\<not> (a\<^sup>2 \<le> n)" 
    hence **:"a\<^sup>2 \<ge> n+1" by auto
    show False proof(cases "a\<^sup>2 = n+1")
      case True
      then show ?thesis using psq by metis
    next
      case False
      hence "a > sqrt(n+1)" using ** 
        by (smt add_leD2 le_antisym of_nat_1 of_nat_le_of_nat_power_cancel_iff one_power2 power2_nat_le_eq_le real_less_lsqrt real_sqrt_lt_0_iff)
      then show ?thesis using a_def by linarith
    qed    
  qed
  moreover have 3:"n < n+1" by auto
  ultimately have  "a \<le> sqrt n \<and> sqrt n < (a+1)" proof -
    have "a \<le> sqrt n" using 1 a_def 
      by (simp add: real_le_rsqrt)
    moreover have "sqrt n < (a+1)" using 2 3 real_le_rsqrt 
      by (smt le_add2 of_nat_1 of_nat_add of_nat_mono of_nat_power_less_of_nat_cancel_iff real_less_lsqrt)
    ultimately show ?thesis by auto
  qed
  hence "\<lfloor>sqrt n\<rfloor> = a" by linarith
  thus ?thesis using a_def by simp
qed



lemma sum_psq_eq_sqrt:
  fixes n::nat 
  shows  "((\<Sum>k \<in> {1..n}.  if psq k then 1 else 0) =  \<lfloor>sqrt n\<rfloor>)"
proof(induct n)
  case 0
  then show ?case by auto
next
  case (Suc m)
  then show ?case proof(cases "psq (Suc m)")
    case True  
    hence "\<lfloor>sqrt (m+1)\<rfloor> = \<lfloor>sqrt m\<rfloor>+1"  using psq_imp_sqrt_suc_suc  by auto
    moreover have "(if psq (Suc m) then 1 else 0) = 1" using True by simp
    ultimately show ?thesis using Suc by auto
  next
    case False
    hence "\<lfloor>sqrt (m+1)\<rfloor> = \<lfloor>sqrt m\<rfloor>" using not_psq_imp_sqrt_suc_eq by simp
    moreover have "(if psq (Suc m) then 1 else 0) = 0" using False by simp
    ultimately show ?thesis using Suc by auto
  qed
qed


lemma sum_div_sum_psq:
  fixes n::nat
  shows  "((\<Sum>k \<in> {1..n}.   \<lfloor>n/k\<rfloor>)) mod 2 = ((\<Sum>k \<in> {1..n}.  if psq k then 1 else 0)) mod 2" 
proof -
  have "(\<Sum>k \<in> {1..n}.  (\<lfloor>n / k \<rfloor>)) mod 2 = (\<Sum>i \<in> {1..n}. divisors(i)) mod 2" using sum_div_sum_divisors by presburger
  also have "... = ((\<Sum>k \<in> {1..n}.  if psq k then 1 else 0)) mod 2" using sum_divisors_eq_sum_psq[of n] by argo
  finally show ?thesis by auto
qed

lemma sum_div_suc_sum_psq:
  fixes n::nat
  shows "((\<Sum>k \<in> {1..Suc n}.  \<lfloor>real (Suc n)/real k\<rfloor>) mod 2) = (((\<Sum>k \<in> {1..n}.  \<lfloor>real n/ real k\<rfloor>)) + (if psq (n+1) then 1 else 0)) mod 2" (is "?A = ?B ")
proof -
  have "?A = ((\<Sum>k \<in> {1..n+1}.  if psq k then 1 else 0)) mod 2" using sum_div_sum_psq[of "Suc n"] by auto
  also have "... = (((\<Sum>k \<in> {1..n}.  if psq k then 1 else 0))  + ((if psq (n+1) then 1 else 0))) mod 2" by auto
  also have "... = (((\<Sum>k \<in> {1..n}.  if psq k then 1 else 0) mod 2)  + ((if psq (n+1) then 1 else 0) mod 2)) mod 2" 
    by (metis (no_types, lifting) mod_add_eq)
  also have "... = (((\<Sum>k \<in> {1..n}.  \<lfloor>real n/ real k\<rfloor>) mod 2 ) + ((if psq (n+1) then 1 else 0) mod 2)) mod 2" using sum_div_sum_psq by metis
  finally show ?thesis using mod_add_eq by metis
qed

lemma soln1:
  fixes n::nat
  shows "even ((\<Sum>k \<in> {1..n}.  \<lfloor>n/k\<rfloor>) +  \<lfloor>sqrt n\<rfloor>) "
proof(induct n)
  case 0
  then show ?case by auto
next
  case (Suc n) 
  then show ?case proof(cases "\<exists>a. n+1 = a\<^sup>2")
    case True
    hence " \<lfloor>sqrt (real n)\<rfloor> + 1 = \<lfloor>sqrt (real (Suc n))\<rfloor>" using psq_imp_sqrt_suc_suc by simp
    moreover have "((\<Sum>k \<in> {1..Suc n}.  \<lfloor>real (Suc n)/real k\<rfloor>) mod 2) = (((\<Sum>k \<in> {1..n}.  \<lfloor>real n/ real k\<rfloor>) ) + 1) mod 2" 
      using sum_div_suc_sum_psq True by simp
    ultimately have  "((\<Sum>k \<in> {1..n}.  \<lfloor>real n/real k\<rfloor>) + \<lfloor>sqrt (real n)\<rfloor>) mod 2 = ((\<Sum>k \<in> {1..Suc n}.  \<lfloor>real (Suc n)/ real k\<rfloor>) + \<lfloor>sqrt (real (Suc n))\<rfloor>) mod 2"      
      by presburger
    thus ?thesis using Suc by (metis odd_iff_mod_2_eq_one)
  next
    case False
    hence " \<lfloor>sqrt (real n)\<rfloor>  = \<lfloor>sqrt (real (Suc n))\<rfloor>" using not_psq_imp_sqrt_suc_eq by simp
    moreover have "((\<Sum>k \<in> {1..n}.  \<lfloor>real n/ real k\<rfloor>) mod 2) = ((\<Sum>k \<in> {1..Suc n}.  \<lfloor>real (Suc n)/real k\<rfloor>) mod 2)" using sum_div_suc_sum_psq False by auto
    ultimately have  "((\<Sum>k \<in> {1..n}.  \<lfloor>real n/real k\<rfloor>) + \<lfloor>sqrt (real n)\<rfloor>) mod 2 = ((\<Sum>k \<in> {1..Suc n}.  \<lfloor>real (Suc n)/ real k\<rfloor>) + \<lfloor>sqrt (real (Suc n))\<rfloor>) mod 2"      
      by presburger
    thus ?thesis using Suc by (metis odd_iff_mod_2_eq_one)
  qed
qed

lemma soln2:
  fixes n::nat
  shows  "even ((\<Sum>k \<in> {1..n}.   \<lfloor>n/k\<rfloor>) +   \<lfloor>sqrt n\<rfloor>)"
proof  -
  have "(\<Sum>k \<in> {1..n}.  (\<lfloor>n / k \<rfloor>)) mod 2 = (\<Sum>i \<in> {1..n}. divisors(i)) mod 2" using sum_div_sum_divisors by presburger
  also have "... = ((\<Sum>k \<in> {1..n}.  if psq k then 1 else 0)) mod 2" using sum_divisors_eq_sum_psq[of n] by argo
  finally have "((\<Sum>k \<in> {1..n}.   \<lfloor>n/k\<rfloor>)) mod 2 = ((\<Sum>k \<in> {1..n}.  if psq k then 1 else 0)) mod 2"
    by auto
  hence  "((\<Sum>k \<in> {1..n}.   \<lfloor> n/ k\<rfloor>) +   \<lfloor>sqrt n\<rfloor>) mod 2 = (((\<Sum>k \<in> {1..n}.  if psq k then 1 else 0) +  \<lfloor>sqrt n\<rfloor>) mod 2)" 
    using mod_add_cong by blast
  thus ?thesis using sum_psq_eq_sqrt[of n] 
    by (metis odd_add odd_iff_mod_2_eq_one)
qed  


lemma card_eq_sum: "card A = sum (\<lambda>x. 1) A"
proof -
  have "plus \<circ> (\<lambda>_. Suc 0) = (\<lambda>_. Suc)"
    by (simp add: fun_eq_iff)
  then have "Finite_Set.fold (plus \<circ> (\<lambda>_. Suc 0)) = Finite_Set.fold (\<lambda>_. Suc)"
    by (rule arg_cong)
  then have "Finite_Set.fold (plus \<circ> (\<lambda>_. Suc 0)) 0 A = Finite_Set.fold (\<lambda>_. Suc) 0 A"
    by (blast intro: fun_cong)
  then show ?thesis
    by (simp add: card.eq_fold sum.eq_fold)
qed

lemma
  shows "(\<Sum>k\<in> S. (\<Sum>d\<in> P k. 1)) = (\<Sum>k\<in> S. card (P k))"
  using card_eq_sum by auto


lemma 
  fixes S::"'a set" and P::"'a \<Rightarrow> 'b set"
  assumes  "finite S" and "\<forall>k. finite (P k)"
  shows "card {(k,d) . k \<in> S  \<and> d \<in> P k  } = (\<Sum>k\<in> S. card (P k))"
proof -
  obtain A::"'a \<Rightarrow> ('a*'b) set" where A:"A = (\<lambda>k. {k} \<times> P k )" by auto
  have "card (\<Union> (A ` S)) = (\<Sum>i\<in>S. card (A i))" proof(rule card_UN_disjoint)
    show "finite S" using assms by auto  
    show "\<forall>i\<in>S. finite (A i)" using assms A by auto
    show "\<forall>i\<in>S. \<forall>j\<in>S. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}" using A by auto
  qed

  moreover have "\<forall>i \<in> S. card (A i) = card (P i)" proof
    fix i
    assume *:"i \<in> S"
    have "A i = {i} \<times> P i" using A by auto
    then show "card (A i) = card (P i)" using * 
      by (simp add: card_cartesian_product_singleton)
  qed
  moreover have "\<Union> (A ` S) =  {(k,d) . k \<in> S  \<and> d \<in> P k  }" unfolding image_def
    apply(auto)
    using A by blast+
  ultimately show ?thesis by auto
qed

end