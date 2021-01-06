theory CourseInNumberTheory
imports Complex_Main Dirichlet_Series.Arithmetic_Summatory Dirichlet_Series.Divisor_Count 
begin

sledgehammer_params[debug=true,timeout=600]

lemma sum_seq:
  fixes n::nat
  shows  "(\<Sum> k \<in> {1..n}. k) = (n+1)*n/2" 
proof(induct n)
case 0
then show ?case by auto
next
  case (Suc n)
  have "(\<Sum> {1..Suc n})  = (\<Sum> {1..n}) + (n+1)" sorry
  also have "... = (n+1)*n/2 + (n+1)" using Suc by auto
  finally show ?case by simp
qed
  
lemma sum_cubes_eq_sq_sum:
  fixes n::nat
  shows "(\<Sum>k \<in> {1..n}.  k^3 )  = (\<Sum>k \<in> {1..n}.  k)^2"
proof(induct n)
case 0
then show ?case by auto
next
  case (Suc n)

 
  have s1: " (n+1) * (\<Sum> k \<in> {1..n}. k) = (n+1)*n*(n+1)/2" using sum_seq by simp
  have s2: " (n+1) * (\<Sum> k \<in> {1..Suc n}. k ) = (n+1)*(n+1)*(n+2)/2" using sum_seq[of "Suc n"] 
    by (metis Suc_1 Suc_eq_plus1 add_Suc_shift mult.assoc mult.commute of_nat_mult times_divide_eq_right)
  have " (n+1)*n*(n+1)/2 + (n+1)*(n+1)*(n+2)/2 = (n+1)^3" 
    by (smt add_mult_distrib2 field_sum_of_halves mult.commute mult_2_right nat_mult_1_right of_nat_add power3_eq_cube)


  have "(\<Sum> k \<in> {1..Suc n}. k )\<^sup>2 = (\<Sum> k \<in> {1..Suc n}. k * (\<Sum> k \<in> {1..Suc n}. k ))" sorry
  also have "... = (\<Sum> k \<in> {1..n}. k * (\<Sum> k \<in> {1..Suc n}. k )) + (n+1) * (\<Sum> k \<in> {1..Suc n}. k )" sorry
  also have "... = (\<Sum> k \<in> {1..n}. k * (n+1 + (\<Sum> k \<in> {1..n}. k ))) + (n+1) * (\<Sum> k \<in> {1..Suc n}. k )" sorry
  also have "... = (\<Sum> k \<in> {1..n}. k * n+1)  + (\<Sum> k \<in> {1..n}. k * (\<Sum> k \<in> {1..n}. k )) + (n+1) * (\<Sum> k \<in> {1..Suc n}. k )" sorry
  also have "... = (n+1) * (\<Sum> k \<in> {1..n}. k) + (\<Sum> k \<in> {1..n}. k * (\<Sum> k \<in> {1..n}. k )) + (n+1) * (\<Sum> k \<in> {1..Suc n}. k )" sorry
  

  also have "... = (\<Sum> k \<in> {1..Suc n}. k * ((n+1) +  (\<Sum> k \<in> {1..n}. k )))" sorry
  also have "... = (\<Sum> k \<in> {1..n}. k * ((n+1) +  (\<Sum> k \<in> {1..n}. k ))) + (n+1)* (n+1) +  k * (\<Sum> k \<in> {1..n}. k ))"
  also have "... = (\<Sum> k \<in> {1..Suc n}. k * (n+1) +  k * (\<Sum> k \<in> {1..n}. k ))" sorry

  then show ?case 
qed


end