%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%An ontology of composite, collectives, and pluralities.
%CEM (classical atomic extensional mereology) + theory of collectives and composites.


%Implemented by Daniele Porello on the basis of the ontology
%developed by Claudio Masolo and Laure Vieu
%with contributions by Stefano Borgo and Roberta Ferrario.

%August 2020

%Proved consistent with Darwin 1.4.4
%Using the Hets environment https://github.com/spechub/Hets

%Reference paper:
%C. Masolo, L. View, R. Ferrario, S. Borgo, D. Porello. "Collectives, Composites and Pluralities". 
%In Formal Ontology in Information Systems - Proceedings of the 11th International Conference, FOIS 2020. (To Appear).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Taxonomy
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_taxonomy, axiom, (![X]: (ob(X) | time(X)))).

fof(ax_taxonomy_disj, axiom, (~?[X]: (ob(X) & time(X)))).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Mereology of objects
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_part_objects_a3, axiom, (![X,Y]: (part(X,Y) => (ob(X) & ob(Y))))).

fof(ax_part_rifl, axiom, (![X]: (ob(X) => part(X,X)))).

fof(ax_part_antisymm, axiom, (![X,Y]: ((part(X,Y) & part(Y,X)) => (Y=X)))).

fof(ax_part_trans, axiom, (![X,Y,Z]: ((part(X,Y) & part(Y,Z)) => part(X,Z)))).

fof(ax_part_overlapping_d8, axiom, (![X,Y]: (overlap(X,Y) <=> ?[Z]:(part(Z,X) & part(Z,Y))))).

fof(ax_part_underlapping, axiom, (![X,Y]: (underlap(X,Y) <=> ?[Z]:(part(X,Z) & part(Y,Z))))).

fof(ax_part_strong_supp, axiom, (![X,Y]: ((ob(X) & ob(Y) & ~ part(Y,X)) => ?[Z]:(part(Z,Y) & ~ overlap(Z,X))))).

fof(ax_part_proper_part, axiom, (![X,Y]: (properPart(X,Y) <=> (part(X,Y) & ~ part(Y,X))))).

%Sum:

fof(ax_part_sum_df, axiom, (![Z,X,Y]: (sum(Z,X,Y) <=> (ob(Z) & ![W]:((overlap(W,Z) <=> (overlap(W,X) | overlap(W,Y)))))))).

fof(ax_part_sum_existence_no_ul, axiom, (![X,Y]: ((ob(X) & ob(Y)) => (?[Z]:(sum(Z,X,Y)))))).

%fof(ax_part_sum_existence_ul, axiom, (![X,Y]: ((ob(X) & ob(Y) & underlap(X,Y)) => ?[Z] : (sum(Z,X,Y))))).

%Product:

fof(ax_part_product_existence, axiom, (![X,Y]: (overlap(X,Y) => (?[Z]:(ob(Z) & ![W]:((part(W,Z) <=> (part(W,X) & part(W,Y))))))))).

%Difference:

fof(ax_part_difference, axiom, (![Z,X,Y]: (difference(Z,X,Y) <=> (((ob(Z) & ![W]: ((part(W,Z) <=> (part(W,X) & ~overlap(W,Y)))))))))).

fof(ax_part_difference_existence, axiom, (![X,Y]: (?[Z]: (part(Z,X) & ~overlap(Z,Y)) => (?[Z1]: (difference(Z1,X,Y)))))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Atoms and atomic parts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Atoms:

fof(ax_atom_d1, axiom, (![X]: (atom(X) <=> (ob(X) & ~(?[Y]:(part(Y,X) & ~(X=Y))))))).

%Atomicity:

fof(ax_atomicity, axiom, (![X]: (ob(X) => (?[Y]: (atom(Y) & part(Y,X)))))).

%Atomic part

fof(ax_atomic_part_d2, axiom, (![X,Y]: (atomicPart(X,Y) <=> (part(X,Y) & atom(X))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Existence, wholly exists, and parthood.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Existence:

fof(ax_existence_a1, axiom, (![X,T]: (exists(X,T) => (ob(X) & time(T))))).

%Objects exist at least at one time:

fof(ax_objects_exist_a2, axiom, (![X]: (ob(X) => ?[T]:(time(T) & exists(X,T))))).

%Wholly exist at time t:

fof(ax_wholly_exist_d3, axiom, ((![X,T]: (existsW(X,T) <=> (![Y]: (part(Y,X) => exists(Y,T))))))).

%Parts and existence:

fof(ax_part_exist_a4, axiom, ((![X,Y,T]: ((exists(X,T) & part(X,Y)) => (exists(Y,T)))))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Pluralities, composites, and collectives
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Pluralities are mereological sums.

%Constitutions: const1 and const2

%const1(X,Y,T) : at time T, the object (a composite) X is constituted(1) by the plurality Y.

%const2(X,Y,T) :  at time T, the object (a collective) X is constituted(2) by the plurality Y.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_const1_a6, axiom, (![X,Y,T]: (const1(X,Y,T) => (exists(X,T) & existsW(Y,T) & atom(X) & ~atom(Y) & time(T))))).

fof(ax_const2_a6, axiom, (![X,Y,T]: (const2(X,Y,T) => (exists(X,T) & existsW(Y,T) & atom(X) & ~atom(Y) & time(T))))).

%Constituted objects are always constituted:

fof(ax_const1_a7, axiom, (![X,T,T1]: ((exists(X,T) & exists(X,T1)) => (?[Y]: const1(X,Y,T) <=> ?[Y1]: const1(X,Y1,T1))))).

fof(ax_const2_a8, axiom, (![X,T,T1]: ((exists(X,T) & exists(X,T1)) => (?[Y]: const2(X,Y,T) <=> ?[Y1]: const2(X,Y1,T1))))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Composite (const 1) and collectives (const 2)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_collective_d4, axiom, (![X]:(collective(X) <=> (![T]: (exists(X,T) => ?[Y]:(const2(X,Y,T))))))).
fof(ax_composite_d5, axiom, (![X]:(composite(X) <=> (![T]: (exists(X,T) => ?[Y]:(const1(X,Y,T))))))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Components of composite (const1) and members of collectives (const2)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_member_d6, axiom, (![X,Y,T]: (member(X,Y,T) <=> (?[Z]: (const2(Y,Z,T) & atomicPart(X,Z)))))).

fof(ax_component_d7, axiom, (![X,Y,T]: (component(X,Y,T) <=> (?[Z]: (const1(Y,Z,T) & atomicPart(X,Z)))))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Collectives, unicity of decomposition
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


fof(ax_const2_unicity_decomposition_a9, axiom, (![X,Y,Z,T]: ((const2(X,Y,T) & const2(X,Z,T))  => (Y=Z)))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Recursive decomposition of const1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


fof(ax_const1_recursive_decomposition_a10, axiom, (![X,Y,Y1,Y2,A,Z,T]: ((const1(X,Y,T) & atomicPart(A,Y) & (const1(A,Z,T) | const2(A,Z,T)) & difference(Y2,Y,A) & sum(Y1,Y2,Z)) => const1(X,Y1,T)))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Composite, covering of const1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_const1_covering_a11, axiom, (![X,Y,Z,T]: ((const1(X,Y,T) & const1(X,Z,T)) => ~(part(Y,Z) & ~(Y=Z))))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Ovelapping condition of (const2) and (const1)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_const1_overlap_a12_1, axiom, (![X,Y,T]: ((const1(X,Y,T))  => (~overlap(X,Y))))).
fof(ax_const2_overlap_a12_2, axiom, (![X,Y,T]: ((const2(X,Y,T))  => (~overlap(X,Y))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Member asymmetry

fof(ax_member_asymm_a13, axiom, (![X,Y,T]: (member(X,Y,T) => ~(member(Y,X,T))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Subcollectives and subcomposite

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


fof(ax_subcollective_d9, axiom, (![X,Y,T]: (subcollective(X,Y,T) <=> (?[A,B]: (const2(X,A,T) & const2(Y,B,T) & part(A,B)))))).

fof(ax_subcomponent_d10, axiom, (![X,Y,T]: (subcomposite(X,Y,T) <=> (?[A,B]: (const1(X,A,T) & const1(Y,B,T) & part(A,B)))))).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Composite, collectives, member, components. Component of collective.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


fof(ax_member_component_a14, axiom, (![X,Y,T]: ((collective(X) & composite(X) & member(Y,X,T)) => (component(Y,X,T))))).

fof(ax_component_subcollective_a15, axiom, (![X,Y,T]: ((collective(X) & composite(X) & component(Y,X,T) & ?[Z]: (component(Z,Y,T) | member(Z,Y,T)) & member(Z,X,T)) => (subcollective(Y,X,T))))).

fof(ax_component_of_collectives_d11, axiom, (![X,Y,T]: (componentOfcollective(X,Y,T) <=> (collective(Y) & composite(Y) & component(X,Y,T) & (member(X,Y,T) | subcollective(X,Y,T)))))).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%THEOREMS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%Mereology:%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(cj_proper_parts_and_sums, conjecture, (![X]: (?[Y]: (properPart(Y,X)) => (?[Y1,Y2]: (sum(X,Y1,Y2)))))). %OK

fof(cj_unicity_sums, conjecture, (![X,Y,Z]: (sum(X,Y,Z) & sum(W,Y,Z)) => X=W)). %OK

fof(cj_extensionality, conjecture, (![X,Y]: ((?[Z]: (properPart(Z,X)) & ?[Z1]: (properPart(Z1,Y))) => ((![W]: (part(W,X) <=> part(W,Y))) => X=Y)))). %OK


%Theorems%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(th_test_irr_components_t1_1, conjecture, ((![T,X]: (~component(X,X,T))))). %OK

fof(th_test_irr_members_t1_2, conjecture, ((![T,X]: (~member(X,X,T))))). %OK.

fof(th_test_trans_components_t2, conjecture, ((![X,Y,Z,T]: ((component(X,Y,T) & component(Y,Z,T)) => component(X,Z,T))))). %The prover fails, but see: test_trans_components_t2.

fof(th_test_trans_member_component_t3, conjecture, ((![X,Y,Z,T]: ((member(X,Y,T) & component(Y,Z,T)) => component(X,Z,T))))). %The prover fails, but see: test_trans_mix_member_component_t3.

fof(th_component_asymm_t4, conjecture, (((![X,Y,T]: ((component(X,Y,T) => ~(component(Y,X,T)))))))). %The prover fails but see: test_asymm_component_t4

fof(th_test_member_overlap_t5, conjecture, ((![X,Y,T]: (member(X,Y,T) => ?[Z] : ((~(overlap(Z,X)) & member(Z,Y,T))))))). %The prover fails, but see: test_memb_overlap_t5

fof(th_test_comp_overlap_t6, conjecture, ((![X,Y,T]: (component(X,Y,T) => ?[Z] : ((~(overlap(Z,X)) & component(Z,Y,T))))))). %The prover fails, but see: test_comp_overlap_t6

fof(th_test_trans_sub_collective_t7, conjecture, ((![X,Y,Z,T]: ((subcollective(X,Y,T) & subcollective(Y,Z,T)) => subcollective(X,Z,T))))). %OK.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Test of theorems:

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%fof(test_trans_component_t2, axiom, ((component(s1,s2,t) & component(s2,s3,t) & ~(component(s1,s3,t))))).  %INCONSISTENT
%fof(test_trans_member_component_t3, axiom, ((member(s1,s2,t) & component(s2,s3,t) & ~(component(s1,s3,t))))).  %INCONSISTENT
%fof(test_asymm_component_t4, axiom, ((component(s1,s2,t) & component(s2,s1,t)))).  %INCONSISTENT
%fof(test_memb_overlap_t5, axiom, (((member(s,c,t)) & ~(?[Z] : ((~(overlap(Z,c)) & member(Z,c,t))))))). %INCONSISTENT
%fof(test_comp_overlap_t6, axiom, (((component(s,c,t)) & ~(?[Z] : ((~(overlap(Z,c)) & component(Z,c,t))))))). %INCONSISTENT
