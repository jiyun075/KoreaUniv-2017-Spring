open Regex 

exception Not_implemented

let rec regex2nfa : Regex.t -> Nfa.t 
=fun regex -> 
let start = Nfa.create_new_nfa() in
let (s_final_fst, start1) = (Nfa.create_state start) in
let base = (Nfa.add_final_state start1 s_final_fst) in
let s_init = (Nfa.get_initial_state base) in
match regex with
| Empty -> base
| Epsilon -> (Nfa.add_epsilon_edge base (s_init, s_final_fst))
| Alpha ab -> (Nfa.add_edge base (s_init, ab, s_final_fst))
| OR (r_t1, r_t2) -> let t1 = regex2nfa r_t1 in
                     let t2 = regex2nfa r_t2 in
                     let new_init = (Nfa.get_initial_state start) in
                     let (new_final, base0) = (Nfa.create_state start) in
                     let base1 = (Nfa.add_final_state base0 new_final) in
                     let base11 = (Nfa.add_states base1 (Nfa.get_states t1)) in
                     let base12 = (Nfa.add_states base11 (Nfa.get_states t2)) in
                     let base13 = (Nfa.add_edges base12 (Nfa.get_edges t1)) in
                     let base14 = (Nfa.add_edges base13 (Nfa.get_edges t2)) in
                     let t1_init = Nfa.get_initial_state t1 in
                     let t2_init = Nfa.get_initial_state t2 in
                     let t1_final_set = (Nfa.get_final_states t1) in
                     let t2_final_set = (Nfa.get_final_states t2) in
                     let base2 = (Nfa.add_epsilon_edge base14 (new_init, t1_init)) in
                     let base3 = (Nfa.add_epsilon_edge base2 (new_init, t2_init)) in
                     let temp_add_e_edge : Nfa.state -> Nfa.t -> Nfa.t
                     = fun state1 t1 -> Nfa.add_epsilon_edge t1 (state1, new_final) in
                     let base4 = (BatSet.fold temp_add_e_edge t1_final_set base3) in
                     let result = (BatSet.fold temp_add_e_edge t2_final_set base4) in
                     result
| CONCAT (r_t1, r_t2) -> let t1 = regex2nfa r_t1 in
                         let t2 = regex2nfa r_t2 in
                         let t1_init = Nfa.get_initial_state t1 in
                         let t2_init = Nfa.get_initial_state t2 in
                         let t1_final_set = Nfa.get_final_states t1 in
                         let t2_final_set = Nfa.get_final_states t2 in
                         let new_init = (Nfa.get_initial_state start) in
                         let base11 = (Nfa.add_states start (Nfa.get_states t1)) in
                         let base12 = (Nfa.add_states base11 (Nfa.get_states t2)) in
                         let base13 = (Nfa.add_edges base12 (Nfa.get_edges t1)) in
                         let base14 = (Nfa.add_edges base13 (Nfa.get_edges t2)) in
                         let base0 = (Nfa.add_epsilon_edge base14 (new_init, t1_init)) in
                         let temp_add_e_edge : Nfa.state -> Nfa.t -> Nfa.t
                         = fun state1 t1 -> Nfa.add_epsilon_edge t1 (state1, t2_init) in
                         let base1 = (BatSet.fold temp_add_e_edge t1_final_set base0) in
                         let temp_add_f_state : Nfa.state -> Nfa.t -> Nfa.t
                         = fun state1 t1 -> Nfa.add_final_state t1 state1 in
                         let result = (BatSet.fold temp_add_f_state t2_final_set base1) in
                         result
| STAR (r_t1) -> let t1 = regex2nfa r_t1 in
                 let t1_init = Nfa.get_initial_state t1 in
                 let t1_final_set = Nfa.get_final_states t1 in
                 let new_init = (Nfa.get_initial_state start) in
                 let (new_final, base0) = (Nfa.create_state start) in   
                 let base1 = (Nfa.add_final_state base0 new_final) in
                 let base00 = (Nfa.add_states base1 (Nfa.get_states t1)) in
                 let base01 = (Nfa.add_edges base00 (Nfa.get_edges t1)) in
                 let base2 = (Nfa.add_epsilon_edge base01 (new_init, t1_init)) in
                 let temp_add_e_edge1 : Nfa.state -> Nfa.t -> Nfa.t  
                 = fun state1 t1 -> Nfa.add_epsilon_edge t1 (state1, new_final) in
                 let temp_add_e_edge2 : Nfa.state -> Nfa.t -> Nfa.t
                 = fun state1 t1 -> Nfa.add_epsilon_edge t1 (state1, t1_init) in
                 let base3 = (BatSet.fold temp_add_e_edge1 t1_final_set base2) in
                 let base4 = (BatSet.fold temp_add_e_edge2 t1_final_set base3) in
                 let result = (Nfa.add_epsilon_edge base4 (new_init, new_final)) in
                 result


let nfa2dfa : Nfa.t -> Dfa.t
=fun nfa -> (* Epsilon Closure *)
            let extension : Nfa.state -> Nfa.states -> Nfa.states
            = fun set1 original_set -> BatSet.union original_set (BatSet.add set1 (Nfa.get_next_state_epsilon nfa set1)) in
            let extension_set : Nfa.states -> Nfa.states
            = fun set2 -> BatSet.fold extension set2 set2 in
            let rec closure : Nfa.states -> Nfa.states
            = fun set3 ->
            let updated_set3 = extension_set set3 in
            let equal = BatSet.equal set3 updated_set3 in
            begin
            match equal with
            | true -> set3
            | false -> closure (updated_set3)
            end in

            (* Find Alphabet Set of Nfa *)
            let (nfa_edge, nfa_eps_edgs) = (Nfa.get_edges nfa) in
            let empty_al_set = BatSet.empty in
            let rec find_alphaset : Nfa.edge list -> alphabet BatSet.t ->  alphabet BatSet.t
            = fun ed alphaset1 ->
            begin
            match ed with
            | [] -> alphaset1
            | (xs1, alpha1, xs2) :: tl -> (BatSet.add alpha1 (find_alphaset tl alphaset1)) 
            end in
            let nfa_alphaset = (find_alphaset nfa_edge empty_al_set) in (* <- alphabet Set of Nfa *)

            (* Create Dfa with initial state *)
            let nfa_init = Nfa.get_initial_state nfa in (* <- Get initial state of Nfa.t *)
            let fst_set = (BatSet.add nfa_init (Nfa.get_next_state_epsilon nfa nfa_init)) in
            let init = closure fst_set in
            let base = Dfa.create_new_dfa init in (* <- base Dfa with initial state*)
            let dd = BatSet.singleton init in (* Initialize set D : states of Dfa.t *)
            let ww = BatSet.singleton init in (* Initialize set W *)

            (* /////////////////// *) 
            (* Subset construction *)
            

            (* For 1 alphabet & 1 Dfa.state -> Find dest.state *)
            let f_dest_s : alphabet -> Dfa.state -> Dfa.state
            = fun aa dfa_s ->
            begin
            let subfun11 : Nfa.state -> Dfa.state -> Dfa.state
            = fun nfa_s0 dfa_ss0 -> (BatSet.union dfa_ss0 (Nfa.get_next_state nfa (nfa_s0) aa)) in
            let subfun12 : Nfa.state -> Dfa.state -> Dfa.state
            = fun nfa_s1 dfa_ss1 -> closure (BatSet.fold subfun11 (closure (BatSet.singleton nfa_s1)) dfa_ss1) in
            let subfun13 : Dfa.state -> Dfa.state -> Dfa.state
            = fun dfa_st2 dfa_ss2 -> closure (BatSet.fold subfun12 dfa_st2 dfa_ss2) in
            let empty_dfa_s = BatSet.empty in
            (subfun13 dfa_s empty_dfa_s)
            end in

            (* For 1 alphabet & 1 Dfa.state -> Updating *)
            let one_update_t : Dfa.state -> alphabet -> (Dfa.states * Dfa.states * Dfa.t) -> (Dfa.states * Dfa.states * Dfa.t)
            = fun q0 a0 (d0, w0, dfa_t0) -> (* Q: 1 element of W/ A: alphabet/ D: set D/ W: set W/ Dfa_t : Dfa.t *)
            begin
            let new_state = (f_dest_s a0 q0) in

            let check_new : Dfa.state -> Dfa.states -> bool (* Check whether state is newly added *)
            = fun s00 ss00 -> (BatSet.mem s00 ss00) in
            let is_new = not (check_new new_state d0) in

            let dfa_t00 = (Dfa.add_state dfa_t0 new_state) in (* Add new state to Dfa.t *)
            let dfa_t01 = (Dfa.add_edge dfa_t00 (q0, a0, new_state)) in (* Add new edge to Dfa.t *)
            let d00 = (BatSet.add new_state d0) in (* Add new state to set D *)
            match is_new with
            | true -> (d00, (BatSet.add new_state w0), dfa_t01)
            | false -> (d00, w0, dfa_t01)
            end in

            (* For Every Alphabet && 1 element of W (Dfa.state q) -> Updating *)
            let all_update_t : Dfa.state -> (Dfa.states * Dfa.states * Dfa.t) -> (Dfa.states * Dfa.states * Dfa.t)
            = fun q1 (d1, w1, dfa_t1) ->
            begin
            let subfun2 : alphabet -> (Dfa.states * Dfa.states * Dfa.t) -> (Dfa.states * Dfa.states * Dfa.t)
            = fun a1 (d10, w10, dfa_t10) -> (one_update_t q1 a1 (d10, w10, dfa_t10)) in
            let (d11, w11, dfa_t11) = (BatSet.fold subfun2 nfa_alphaset (d1, w1, dfa_t1)) in
            (d11, (BatSet.remove q1 w11), dfa_t11) (* remove q from w *)
            end in

            (* For Every Alphabet && Every element of W -> Updating *)
            let rec subset_const : (Dfa.states * Dfa.states * Dfa.t) -> (Dfa.states * Dfa.states * Dfa.t)
            = fun (d2, w2, dfa_t2) ->
            begin
            let (d20, w20, dfa_t20) = (BatSet.fold all_update_t w2 (d2, w2, dfa_t2)) in
            let w_isempty = BatSet.is_empty w20 in
            match w_isempty with
            | true -> (d20, w20, dfa_t20)
            | false -> (subset_const (d20, w20, dfa_t20))
            end in

            (* /////////////////////////// *)
            (* Add Final State to Dfa.t *)

            let nfa_fin = (Nfa.get_final_states nfa) in (* Get final_states of Nfa.t *)

            (* For 1 Nfa.final_state & 1 Dfa.state -> Adding *)
            let one_add_fin : Nfa.state -> Dfa.state -> Dfa.t -> Dfa.t
            = fun one_nfa_s0 q3 dfa_t3 -> 
            begin
            let isfin = (BatSet.mem one_nfa_s0 q3) in
            match isfin with
            | true -> (Dfa.add_final_state dfa_t3 q3)
            | false -> dfa_t3
            end in

            (* For every Nfa.final_state & 1 Dfa.state -> Adding *)
            let all_add_fin : Dfa.state -> Dfa.t -> Dfa.t
            = fun q4 dfa_t4 -> 
            begin
            let subfun3 : Nfa.state -> Dfa.t -> Dfa.t
            = fun one_nfa_s1 dfa_t40 -> (one_add_fin one_nfa_s1 q4 dfa_t40) in
            (BatSet.fold subfun3 nfa_fin dfa_t4)
            end in

            (* For every Nfa.final_state & every Dfa.state -> Adding *)
            let full_add_fin : Dfa.states -> Dfa.t -> Dfa.t
            = fun d5 dfa_t5 -> (BatSet.fold all_add_fin d5 dfa_t5) in

            (* ////////////////////////////// *)

            (* Return Dfa.t *)
            let (d_fin, w_fin, dfa_fin) = subset_const (dd, ww, base) in
            let dfa_final = full_add_fin d_fin dfa_fin in
            dfa_final

(* Do not modify this function *)
let regex2dfa : Regex.t -> Dfa.t
=fun regex -> 
  let nfa = regex2nfa regex in
  let dfa = nfa2dfa nfa in
    dfa

let run_dfa : Dfa.t -> alphabet list -> bool
= fun dfa str -> let init = Dfa.get_initial_state dfa in
                 let temp_get_next_state : alphabet -> Dfa.state ->  Dfa.state
                 = fun a0 s0 -> (Dfa.get_next_state dfa s0 a0) in
                 let t_gns_default a1 s1 = 
                 try temp_get_next_state a1 s1
                 with Failure _ -> BatSet.empty in
                 let rec find_final : alphabet list -> Dfa.state -> Dfa.state
                 = fun a_lst s2 -> 
                 begin
                 match a_lst with
                 | [] -> s2
                 | hd :: tl -> if (BatSet.is_empty (t_gns_default hd s2)) then BatSet.empty
                               else (find_final tl (t_gns_default hd s2))
                 end in
                 let fin_state = (find_final str init) in
                 (Dfa.is_final_state dfa fin_state)
