;--- Evacuation train station model for the H2020 IMPACT project ---
;--- Made by dr. C. Natalie van der Wal ---
;--- 31st May 2016 --


;2.10.7
;- FIXED BUG: comments in INFO Tab were too long. It was necessary reduce it, otherwise the software do not open.

;2.10.6
;- Refactoring the comments.
;

;2.10.5
; FIXED BUG: group formation and how to calculate the proportions.
; FIXED BUG: changed the way to avoid fire, in some situations when the fire is close to the door,
;            agents try to scape to out of world, what generats an error in the code in the previous version.

;2.10.4
; added placing passengers on white or orange at initialisation (otherwise when emergency lighting is on, there arent enough white patches for initialising 3200 passengers)

;2.10.3
; added cutural_cluster settingsin interface (necessary for behaviorspace)


;2.10.2
; BEHAVIOR SPACE ADJUST: added variables to interface to enable behavior space control them.

;2.10.1
; BUG FIX: avoid form groups with children when their list is empty.

;2.10.0
;
;- added compliance level matrix (config file)
;  with setup function in the model / internal state
;- social identity: updated the funcion. Now based on cultural cluster and group membership only
;- updated the emergency lighting in config file
;- updated the fall chance reducing it for a more realistic pattern
;- staff place in the doors equally
;- fire position configurable, including (start to evacuate without fire). See PLACE_FIRE_POSITION
;- FIXED BUG: speed setted up according to age and genre. Before that it was never fixed due to an error
;- FIXED BUG: in avoid fire changed the way to see the fire to dont be stucked

;2.9.8
;
; history updating started.


;-----------------------------------------
;GLOBALS
;INITIALISATION PART 1
;INITIALISATION PART 2
;GO
;MODEL
;AUXILLIARY MODEL FUNCTIONS
;GENERAL AUXILLIARY FUNCTIONS
;INTERFACE FUNCTIONS
;PLOTS
;-----------------------------------------

extensions [matrix] ; extension to add helping chance matrix.
__includes [ "config.nls" ]

breed [staff staff_member]
breed [agents agent]
directed-link-breed [help-links help-link]


;-----------------------------------------
;GLOBALS
;-----------------------------------------

globals [; GLOBALS
         helping_chance_matrix compliance_level_matrix
         main_entrance_target total_number_of_survivors staff_instructions sound_fire_alarm sound_public_announcement room_environment_filename list_exits start_place_fire start_observation_fire start_fire_alarm place_fire_tick
         lighting_list ;nw
         ; _public_announcement _fire_alarm number_staff_members
         current_time days hours minutes seconds ;nw
         public_announcement_frequency alarm_frequency pa_count_seconds alarm_count_seconds;nw

         cultural_cluster_distribution ;nw
         cultural_cluster ;nw
         english_proficiency ;nw

         ; WEIGHTS
         W_sensing_fire
         W_sensing
         W_affectivebiasing
         W_persisting
         W_complying
         W_amplifyingfeeling
         W_inhibitingfeeling
         W_amplifyingevacuation
         W_inhibitingwalkrand
         W_decreasingintention
         W_amplifyingintention
         W_decreasingfear

         ; STATISTICS
         statistics_evacuated_door1 statistics_evacuated_door2 statistics_evacuated_door3 statistics_evacuated_door4
         statistics_average_walking_speed statistics_average_running_speed statistics_maximum_running_speed statistics_minimum_running_speed statistics_maximum_walking_speed  statistics_minimum_walking_speed

         statistics_average_resp_time_from_decide_evacuate_cumulative statistics_average_resp_time_from_start_fire_cumulative

         statistics_average_resp_time_from_decide_evacuate statistics_average_resp_time_from_start_fire      statistics_average_resp_time_from_observation_fire      statistics_average_resp_time_from_fire_alarm      statistics_average_resp_time_from_contagion
         statistics_average_resp_time_from_start_fire_died statistics_average_resp_time_from_observation_fire_died statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_contagion_died
         divisor_after_fire_alarm divisor_after_observation_fire divisor_after_contagion

         statistics_average_fear statistics_average_belief_dangerous statistics_average_intention_evacuate statistics_average_intention_walkrand statistics_average_desire_evacuate statistics_average_desire_walkrand
         statistics_falls_total statistics_falls_average_per_passenger statistics_evacuation_time
         statistics_hist_observeFire statistics_hist_contagion statistics_hist_fireAlarm

         START_FIRE_ALARM_ACTION START_PA_ACTION START_FIRE_ACTION
         END_OF_SIMULATION
         EXIT_COLOR EXIT_LIGHTING_COLOR STAFF_COLOR PASSENGERS_COLOR DEAD_PASSENGERS_COLOR FALL_COLOR START_EVACUATE_COLOR FIRE_RADIUS FIRE_COLOR PROTOCOL_DISTANCE OBSERVATION_DISTANCE L_STEEPNESS L_THRESHOLD AL_STEEPNESS AL_THRESHOLD ETA_MENTAL ETA_BODY CROWD_CONGESTION_THRESHOLD


         g_st_others_belief_dangerous
         g_st_others_fear

         g_st_observation_fire
         g_st_observation_alarm
         g_st_observation_others_belief_dangerous
         g_st_observation_others_fear
         g_st_observation_staff_instr
         g_st_observation_pa

         g_st_agent_location
         g_st_fear

         g_st_belief_dangerous
         g_st_compliance

         g_st_dead
         g_st_fall
         g_st_desire_walkrand
         g_st_desire_evacuate
         g_st_intention_walkrand
         g_st_intention_evacuate
         g_st_familiarity

         g_st_express_belief_dangerous
         g_st_express_fear
         g_st_action_walkrandom
         g_st_action_movetoexit
      ]

links-own [relationship_strenght]

; INTERNAL VARIABLES OF EACH AGENT
agents-own [ nearest_exit_target speed speed_bkp ticks-since-fall start_evacuate start_evacuate_flag count_time_stoped_same_position congestion_speed_factor statistics_hist_counted
              agent_to_help
              current_speed

              st_others_belief_dangerous
              st_others_fear

              st_observation_fire
              st_observation_alarm
              st_observation_others_belief_dangerous
              st_observation_others_fear
              st_observation_staff_instr
              st_observation_pa

              st_agent_location
              st_fear

              st_belief_dangerous
              st_compliance
              ;nw added gender and age and group
              st_gender ; can be a female or male passenger, male = 1; female = 0
              st_age    ; can be adult or child, child = 0; adult = 1;  eldery = 2
              st_cultural_cluster
              st_english_proficiency
              st_group_member ; 0 is not a group member, or 1 a group member
              st_leader ; 0 is not a leader, 1 is a leader, each group has only 1 leader and must be an adult.

              st_dead
              st_fall
              ;nw added st_helping
              st_helping ; 0=not helping; 1 = helping
              st_desire_walkrand
              st_desire_evacuate

              st_intention_walkrand
              st_intention_evacuate
              st_familiarity

              st_express_belief_dangerous
              st_express_fear
              st_action_walkrandom
              st_action_movetoexit
          ]




;-----------------------------------------
;INITIALISATION PART 1
;-----------------------------------------
to setup
  clear-all
  ;random-seed

  set list_exits []
  set start_place_fire 0
  set start_observation_fire 0
  set start_fire_alarm 0
  set place_fire_tick  0

  set cultural_cluster    [ "Arab" "Near East" "Latin Amerca" "East Europe" "Latin Europe" "Nordic" "Germanic" "African" "Anglo" "Confucian" "Far East"] ;nw
  set english_proficiency [0.140 0.211 0.0751 0.1628 0.3605 0.8601 0.6951 0.4826 0.9539 0.0156 0.1827] ;nw

  ; STATISTICS
  set statistics_average_walking_speed                        0
  set statistics_maximum_walking_speed                        0
  set statistics_minimum_walking_speed                        0
  set statistics_average_running_speed                        0
  set statistics_maximum_running_speed                        0
  set statistics_minimum_running_speed                        0

  set statistics_evacuated_door1                              0
  set statistics_evacuated_door2                              0
  set statistics_evacuated_door3                              0
  set statistics_evacuated_door4                              0

  set statistics_average_resp_time_from_decide_evacuate            0
  set statistics_average_resp_time_from_decide_evacuate_cumulative 0
  set statistics_average_resp_time_from_start_fire                 0
  set statistics_average_resp_time_from_start_fire_cumulative      0

  set statistics_average_resp_time_from_start_fire_died       0
  set statistics_average_resp_time_from_observation_fire_died 0
  set statistics_average_resp_time_from_fire_alarm_died       0
  set statistics_average_resp_time_from_contagion_died        0
  set divisor_after_fire_alarm                                0
  set divisor_after_observation_fire                          0
  set divisor_after_contagion                                 0

  set statistics_falls_total                 0
  set statistics_falls_average_per_passenger 0
  set statistics_evacuation_time             0


  set statistics_average_fear               0
  set statistics_average_belief_dangerous   0
  set statistics_average_intention_evacuate 0
  set statistics_average_intention_walkrand 0

  set g_st_others_belief_dangerous                    0
  set g_st_others_fear                                0

  set g_st_observation_fire                           0
  set g_st_observation_alarm                          0
  set g_st_observation_others_belief_dangerous        0
  set g_st_observation_others_fear                    0
  set g_st_observation_staff_instr                    0
  set g_st_observation_pa                             0

  set g_st_agent_location                             0
  set g_st_fear                                       0

  set g_st_belief_dangerous                           0
  set g_st_compliance                                 0

  set g_st_dead                                       0
  set g_st_fall                                       0
  set g_st_desire_walkrand                            0
  set g_st_desire_evacuate                            0

  set g_st_intention_walkrand                         0
  set g_st_intention_evacuate                         0
  set g_st_familiarity                                0

  set g_st_express_belief_dangerous                   0
  set g_st_express_fear                               0
  set g_st_action_walkrandom                          0
  set g_st_action_movetoexit                          0


  ; ENVIRONMENT INITIAL CONDITION
  setup-environment

  set statistics_hist_observeFire []
  set statistics_hist_contagion   []
  set statistics_hist_fireAlarm   []
  repeat END_OF_SIMULATION [
    set statistics_hist_observeFire lput 0 statistics_hist_observeFire
    set statistics_hist_contagion   lput 0 statistics_hist_contagion
    set statistics_hist_fireAlarm   lput 0 statistics_hist_fireAlarm
  ]

  if member? "square"    room_environment_filename [resize-world -10 10 -10 10]
  if member? "rectangle" room_environment_filename [resize-world -20 20 -10 10]

  if (member? "2" room_environment_filename) and (member? "left_right" room_environment_filename)[
    set list_exits lput (patch min-pxcor 0) list_exits
    set list_exits lput (patch max-pxcor 0) list_exits
  ]

  if (member? "2" room_environment_filename) and (member? "up_down" room_environment_filename)[
    set list_exits lput (patch 0 min-pycor) list_exits
    set list_exits lput (patch 0 max-pycor ) list_exits
  ]


  if (member? "4" room_environment_filename) and (member? "main_left" room_environment_filename) [
    set list_exits lput (patch min-pxcor 0) list_exits
    set list_exits lput (patch max-pxcor 0) list_exits
    set list_exits lput (patch 0 min-pycor) list_exits
    set list_exits lput (patch 0 max-pycor ) list_exits
  ]

  if (member? "4" room_environment_filename) and (member? "main_down" room_environment_filename) [
    set list_exits lput (patch 0 min-pycor) list_exits
    set list_exits lput (patch 0 max-pycor ) list_exits
    set list_exits lput (patch min-pxcor 0) list_exits
    set list_exits lput (patch max-pxcor 0) list_exits
  ]

  set main_entrance_target item 0 list_exits

  import-pcolors room_environment_filename
  ask patches with [pcolor != white and pcolor != EXIT_LIGHTING_COLOR] [set pcolor EXIT_COLOR] ;nw

  if _exit_lighting = TRUE [
    foreach lighting_list [
      let ix [pxcor] of item 0 ?
      let iy [pycor] of item 0 ?
      let ex [pxcor] of item 1 ?
      let ey [pycor] of item 1 ?

      ifelse ix != ex and iy != ey [ ; diagonal
        while [ix != ex and iy != ey] [
          ifelse ix < ex [set ix ix + 1] [set ix ix - 1]
          ifelse iy < ey [set iy iy + 1] [set iy iy - 1]
          ask patches with [pxcor = ix and pycor = iy] [set pcolor EXIT_LIGHTING_COLOR]
        ]
      ]
      [
        while [ix != ex or iy != ey] [
          if ix < ex and iy = ey [set ix ix + 1]
          if ix > ex and iy = ey [set ix ix - 1]
          if ix = ex and iy < ey [set iy iy + 1]
          if ix = ex and iy > ey [set iy iy - 1]
          ask patches with [pxcor = ix and pycor = iy] [set pcolor EXIT_LIGHTING_COLOR]
        ]
      ]
    ] ;nw
  ]

  set-default-shape agents "person"
  create-agents number_passengers [ move-to one-of patches with [ (pcolor = white or pcolor = orange) and count agents-here < 8 ] ]
  ask agents [
    set color PASSENGERS_COLOR
    set heading random 360
  ]
  ask agents [set ticks-since-fall 0 ]

  ; MODEL INITIAL CONDITION
  setup-passengers
  setup-model

  reset-ticks
  set-time   ;nw
end

;-----------------------------------------
;INITIALISATION PART 2
;-----------------------------------------

to setup-passengers
  ask agents [
    set start_evacuate 0
    set start_evacuate_flag 0
    set count_time_stoped_same_position 0
    set congestion_speed_factor 1
    set statistics_hist_counted 0
    set agent_to_help                          nobody
    set pa_count_seconds           0
    set alarm_count_seconds        0


    set st_cultural_cluster                    -1
    set st_english_proficiency                 -1


    set st_others_belief_dangerous             0
    set st_others_fear                         0

    set st_observation_fire                    0
    set st_observation_alarm                   0
    set st_observation_others_belief_dangerous 0
    set st_observation_others_fear             0
    set st_observation_staff_instr             0
    set st_observation_pa                      0

    ;nw added set st_age and set st_gender and changed location
    set st_gender                              1 ;male
    set st_age                                 1 ;adult
    set st_agent_location                      one-of patches
    set st_group_member                        0
    set st_leader                              0

    set st_fear                                0

    set st_belief_dangerous                    0
    set st_compliance                          0

    set st_dead                                0
    set st_fall                                0
    ;nw added st_helping
    set st_helping                             0
    set st_desire_walkrand                     0
    set st_desire_evacuate                     0

    set st_intention_walkrand                  0
    set st_intention_evacuate                  0

    set st_familiarity                         0

    set st_express_belief_dangerous            0
    set st_express_fear                        0
    set st_action_walkrandom                   0
    set st_action_movetoexit                   0
  ]

  ;nw GROUP DISTRIBUTION
  ask N-of round ((_percentage_females / 100) * number_passengers) agents [set st_gender 0] ;female
  if _percentage_children + _percentage_eldery > 100 [
    user-message "The sum of children and eldery percentage must be between 0 and 100%. The default option is used: 10% children, 10% eldery"
    set _percentage_children 10
    set _percentage_eldery   10
  ]
  ask N-of round ((_percentage_females  / 100) * number_passengers) agents [set st_gender 0] ;female
  ask N-of round ((_percentage_children / 100) * number_passengers) agents [set st_age 0]    ;child
  ask N-of round ((_percentage_eldery   / 100) * number_passengers) agents [set st_age 2]    ;eldery
  ask agents [ if st_age = 0  [set size size / 2]]

  let i 0
  while [i < length cultural_cluster_distribution] [
    let value item i cultural_cluster_distribution
    ask N-of floor (value * number_passengers) agents with [st_cultural_cluster = -1] [
      set st_cultural_cluster    i
      set st_english_proficiency i
    ]
    set i i + 1
  ]

  ask agents with [st_cultural_cluster = -1] [
    set st_cultural_cluster    random length cultural_cluster_distribution
    set st_english_proficiency st_cultural_cluster
  ]


  if _groups_of_2_ratio + _groups_of_3_ratio + _groups_of_4_ratio != 100 [
    user-message "Your group ratios might fit 100% of people traveling in group. The ratios are set to default: groups of 2 = 50% groups of 3 = 30% and groups of 4 = 20%"
    set _groups_of_2_ratio 50
    set _groups_of_3_ratio 30
    set _groups_of_4_ratio 20
  ]

  if _percentage_people_traveling_alone > (100 - (_percentage_children * 2)) [
    user-message "Your % travelling alone is not possible in combination with % of children. The default option is used: traveling alone 50%, children 10%"
    set _percentage_people_traveling_alone 50
    set _percentage_children               10
  ]

   let available_people round ((100 - _percentage_people_traveling_alone) / 100 * number_passengers)

   let people_in_group2 floor (_groups_of_2_ratio * available_people / 100)
   let people_in_group3 floor (_groups_of_3_ratio * available_people / 100)
   let people_in_group4 floor (_groups_of_4_ratio * available_people / 100)

   let people_in_group2_mod people_in_group2 mod 2
   let people_in_group3_mod people_in_group3 mod 3
   let people_in_group4_mod people_in_group4 mod 4

   set people_in_group2 people_in_group2 - people_in_group2_mod
   set people_in_group3 people_in_group3 - people_in_group3_mod
   set people_in_group4 people_in_group4 - people_in_group4_mod
   let rest_tmp people_in_group2_mod + people_in_group3_mod + people_in_group4_mod

   ; the max # of people in rest_tmp will be between 0 and 6.
   if rest_tmp = 5       [set people_in_group4 people_in_group4 + 4        set rest_tmp 1]
   if rest_tmp mod 4 = 0 [set people_in_group4 people_in_group4 + rest_tmp set rest_tmp 0]
   if rest_tmp mod 3 = 0 [set people_in_group3 people_in_group3 + rest_tmp set rest_tmp 0]
   if rest_tmp mod 2 = 0 [set people_in_group2 people_in_group2 + rest_tmp set rest_tmp 0]

   ; the children are divided equally
   let num_children (number_passengers * _percentage_children / 100)
   let people_in_group2_child_plus_parent floor ((num_children * _groups_of_2_ratio / 100) * 2) ; one tirdh part of children to group of 2. The  * 2 is to guarantee one adult per children
   let people_in_group2_adults            people_in_group2 - (people_in_group2_child_plus_parent / 2)

   let people_in_group3_child_plus_parent floor ((num_children * _groups_of_3_ratio / 100) * 3); one tirdh part of children to group of 3. The  * 3 is to guarantee two adults per children
   let people_in_group3_adults            people_in_group3 - (people_in_group3_child_plus_parent / 3)

   let people_in_group4_child_plus_parent floor ((num_children * _groups_of_4_ratio / 100) * 2) ; one tirdh part of children to group of 4. The  * 2 is to guarantee two adults for each 2 children.
   let people_in_group4_adults            people_in_group4 - (people_in_group4_child_plus_parent / 2)

  let children_list []
  ask agents with [st_age = 0] [set children_list lput self children_list]

  ; groups of 2
  let cnt 0
  repeat people_in_group2_child_plus_parent / 2 [ ; divided by 2 because every time in the loop we take 2 people, so to guarante the number of people in this group we have to run it half of the number of people in the group
    if length children_list > 0 [
      let child item 0 children_list
      ask child  [set st_group_member 1]
      let p_tmp one-of agents with [st_age != 0 and st_group_member = 0]
      ask p_tmp  [set st_group_member 1 set st_leader 1]
      create-relationship p_tmp child 1
      set children_list remove-item 0 children_list
      set cnt cnt + 1  ; 1 adults per group with a child.
    ]
  ]

  let ntime (people_in_group2_adults - cnt) / 2
  repeat ntime [ ; same here, and also for the other group, divided by 3 and divided by 4
    if count agents with [st_age != 0 and st_group_member = 0] < 2 [stop]
    let p_tmp1 one-of agents with [st_age != 0 and st_group_member = 0]
    ask p_tmp1 [set st_group_member 1 set st_leader 1]
    let p_tmp2 one-of agents with [st_age != 0 and st_group_member = 0]
    ask p_tmp2 [set st_group_member 1]
    create-relationship p_tmp1 p_tmp2 1
  ]

  ; groups of 3
  set cnt 0
  repeat people_in_group3_child_plus_parent / 3 [
    if length children_list > 0 [
      let child item 0 children_list
      ask child  [set st_group_member 1]
      let p_tmp1 one-of agents with [st_age != 0 and st_group_member = 0]
      ask p_tmp1 [set st_group_member 1 set st_leader 1]
      let p_tmp2 one-of agents with [st_age != 0 and st_group_member = 0]
      ask p_tmp2 [set st_group_member 1]
      create-relationship p_tmp1 child  1
      create-relationship p_tmp2 child  1
      create-relationship p_tmp1 p_tmp2 1
      set children_list remove-item 0 children_list
      set cnt cnt + 2 ; 2 adults per group with a child.
    ]
  ]

  set ntime (people_in_group3_adults - cnt) / 3

  repeat ntime [
    if length children_list > 0 [
      if count agents with [st_age != 0 and st_group_member = 0] < 3 [stop]
      let p_tmp1 one-of agents with [st_age != 0 and st_group_member = 0]
      ask p_tmp1 [set st_group_member 1 set st_leader 1]
      let p_tmp2 one-of agents with [st_age != 0 and st_group_member = 0]
      ask p_tmp2 [set st_group_member 1]
      let p_tmp3 one-of agents with [st_age != 0 and st_group_member = 0]
      ask p_tmp3 [set st_group_member 1]
      create-relationship p_tmp1 p_tmp2 1
      create-relationship p_tmp1 p_tmp3 1
      create-relationship p_tmp2 p_tmp3 1
    ]
  ]

  ; group 4
  set cnt 0
  while [length children_list >= 2] [
    let child1 item 0 children_list
    ask child1 [set st_group_member 1]
    let child2 item 1 children_list
    ask child2 [set st_group_member 1]
    let p_tmp1 one-of agents with [st_age != 0 and st_group_member = 0]
    ask p_tmp1 [set st_group_member 1 set st_leader 1]
    let p_tmp2 one-of agents with [st_age != 0 and st_group_member = 0]
    ask p_tmp2 [set st_group_member 1]
    create-relationship p_tmp1 child1 1
    create-relationship p_tmp1 child2 1
    create-relationship p_tmp1 p_tmp2 1
    create-relationship p_tmp2 child1 1
    create-relationship p_tmp2 child2 1
    create-relationship child1 child2 1
    set children_list remove-item 0 children_list
    set children_list remove-item 0 children_list
    set cnt cnt + 2
  ]

  set ntime (people_in_group4_adults - cnt) / 4
  repeat ntime [
    if count agents with [st_age != 0 and st_group_member = 0] < 4 [stop]
    let p_tmp1 one-of agents with [st_age != 0 and st_group_member = 0]
    ask p_tmp1 [set st_group_member 1 set st_leader 1]
    let p_tmp2 one-of agents with [st_age != 0 and st_group_member = 0]
    ask p_tmp2 [set st_group_member 1]
    let p_tmp3 one-of agents with [st_age != 0 and st_group_member = 0]
    ask p_tmp3 [set st_group_member 1]
    let p_tmp4 one-of agents with [st_age != 0 and st_group_member = 0]
    ask p_tmp4 [set st_group_member 1]
    create-relationship p_tmp1 p_tmp2 1
    create-relationship p_tmp1 p_tmp3 1
    create-relationship p_tmp1 p_tmp4 1
    create-relationship p_tmp2 p_tmp3 1
    create-relationship p_tmp2 p_tmp4 1
    create-relationship p_tmp3 p_tmp4 1
  ]

  ; if some child is alone, link it to a parent
  foreach children_list [
    let child item 0 children_list
    ask child  [set st_group_member 1]
    let p_tmp one-of agents with [st_age != 0 and st_group_member = 0]
    ask p_tmp  [set st_group_member 1]
    create-relationship p_tmp child 1
    set children_list remove-item 0 children_list
  ]


  ; OTHERS PARAMETERS
  ask n-of round ((_percentage_familiarity / 100) * number_passengers) agents [set st_familiarity  1]

  ask agents [
    ;nw adult females walk or run 10% less fast than adult males
    ;nw children walk or run 50% from the maximum speed = speed of adult males
    if st_gender = 0 and st_age = 1 ;female adult
    [set speed 0.9 + random-float 0.52]

    if st_gender = 1 and st_age = 1 ;male adult
    [set speed 1 + random-float 0.52]

    if st_age = 0 ;child
    [set speed 0.5 + random-float 0.5]

    if st_gender = 0 and st_age = 2 ;eldery female
    [set speed 0.9 + random-float 0.22]

    if st_gender = 1 and st_age = 2 ;eldery male
    [set speed 0.9 + random-float 0.3]

    set speed_bkp speed
  ]
end

to create-relationship [who1 who2 strenght]
  if who1 = nobody or who2 = nobody [show "ERROR: create-relationship: agent does not exist" stop]

  ask who1 [create-link-with who2]
  ask links [
    set relationship_strenght strenght
    set thickness 0.1
  ]

  ; move them close each other on the map
  let p [patch-here] of who1
  ask who2 [move-to p]

  place-staff ;nw
end

;-----------------------------------------
;GO
;-----------------------------------------
to go
 if ticks = END_OF_SIMULATION [stop]

 control-experiments

 ask agents [ ; UPDATE ACTIONS
   ;nw prevent a not leader of a group be stopped/lost if the leader is die
   if st_leader = 0 and st_group_member = 1 [
     if count link-neighbors with [st_leader = 1] = 0 [set st_group_member 0 set speed speed_bkp]
   ]


   check-dead-by-fire
   if st_dead = 0 [
      if st_group_member = 0 or st_leader = 1 [;nw do it for alone passengers or to leader group. In a group just the leaders moves, others follow it.
      if start_evacuate > 0 [ move-to-exit ];nw
       move-agent
     ]
      check-fall
      check-get-up
      express
      if _help = TRUE [check-decide-to-help]
      if start_evacuate != 0 and st_fall = 0 [set color START_EVACUATE_COLOR]
    ]
 ]


 ask staff [move-staff] ;nw
 check-exit
 calculate-model  ; UPDATE THE MODEL]

 if pa_count_seconds >= public_announcement_frequency [set pa_count_seconds 0]
 if alarm_count_seconds >= alarm_frequency [set alarm_count_seconds 0]

 ;nw
 set-time
 ask agents with [color = DEAD_PASSENGERS_COLOR] [ if [pcolor] of patch-here != red [die]]
 ask agents with [speed = 0 and st_fall = 0 and count links = 0 and agent_to_help = nobody] [set speed speed_bkp] ;this is a 'safety'line, to make sure all agents keep evacuating if they are not helping and not walking randomly (because we had bugs with some agents not evacuating)

 do-plots         ; UPDATE STATISTICS

 set statistics_evacuation_time ticks - place_fire_tick
 set statistics_average_resp_time_from_start_fire      statistics_average_resp_time_from_start_fire_cumulative      / (number_passengers - count agents with [color = DEAD_PASSENGERS_COLOR]) ;nw
 set statistics_average_resp_time_from_decide_evacuate statistics_average_resp_time_from_decide_evacuate_cumulative / (number_passengers - count agents with [color = DEAD_PASSENGERS_COLOR]) ;nw

 if count turtles with [color != DEAD_PASSENGERS_COLOR] =  0 [stop]  ;nw

 check-fire-alarm ; UPDATE ENVIRONMENT
 check-public-announcement

 tick
end


;-----------------------------------------
;MODEL
;-----------------------------------------
to calculate-model
  ask agents [
    ;
    ; ENVIRONMENTAL INPUTS STATES
    ;

    ; crowd_congestion_location: see function check-fall
    ; fire_location: see button make fire
    ;
    let list_agents agents in-radius OBSERVATION_DISTANCE
    let aggsum_belief 0
    let aggsum_fear 0
    let aggw 0
    ask list_agents [
      set aggsum_belief aggsum_belief + st_express_belief_dangerous * 1
      set aggsum_fear aggsum_fear     + st_express_fear * 1
      set aggw aggw + 1; we do +1 for now, meaning all relationships are 1 for now. in next version something like: sum [relationship_strenght] of links  /todo
    ]

    ifelse _contagion_model = TRUE [
      set st_others_belief_dangerous aggsum_belief / aggw
      set st_others_fear aggsum_fear / aggw
    ]
    [
      set st_others_belief_dangerous 0
      set st_others_fear 0
    ]
    ifelse st_desire_evacuate >= st_desire_walkrand and st_intention_evacuate > st_intention_walkrand and color = START_EVACUATE_COLOR and any? staff in-radius OBSERVATION_DISTANCE
    [set staff_instructions 1] ;nw
    [set staff_instructions 0] ;nw
    ; public_announcement: see function public-announcement

    ;
    ; OBSERVATION STATES
    ;

    ;if the passenger entered the radius one time, the observation_fire is set to 1, but if he leaves it, it will stay one. With ifelse, you could set it back to 0
    if any? patches in-radius OBSERVATION_DISTANCE with [ pcolor = FIRE_COLOR ] [ ;df
      ; if it is the first time, count it in the histogram
      if st_observation_fire = 0 and statistics_hist_counted = 0 [
        let newval item ticks statistics_hist_observeFire
        set statistics_hist_observeFire replace-item ticks statistics_hist_observeFire (newval + 1)
        set statistics_hist_counted 1 ;observed fire = 1
      ]
      set st_observation_fire 1
      if start_observation_fire = 0 [set start_observation_fire ticks]
    ]
    ifelse sound_fire_alarm = 1 [
      if alarm_count_seconds = START_FIRE_ACTION [ ;nw
;      if alarm_count_seconds >= alarm_frequency [ ;nw
        if random 10 > 5 [set st_observation_alarm sound_fire_alarm] ;nw only 50% of time the belief dangerous becomes 1 after observation alarm. ;nw //df db
      ]

      ; fire alarm activated and observed. If it is still not aware of the danger, it becomes aware now and count the ticks.
      if st_observation_fire = 0 and statistics_hist_counted = 0 [
        let newval item ticks statistics_hist_fireAlarm
        set statistics_hist_fireAlarm replace-item ticks statistics_hist_fireAlarm (newval + 1)
        set statistics_hist_counted 3 ; fire alarm = 3
      ]
    ]
    [
      set st_observation_alarm 0
    ]
    set st_observation_others_belief_dangerous st_others_belief_dangerous
    set st_observation_others_fear st_others_fear
    set st_observation_staff_instr staff_instructions

    ;nw
    if sound_public_announcement = 1 [
    ;if pa_count_seconds >= public_announcement_frequency [ ; Public anouncements are considered according to frequecy
      if pa_count_seconds = START_FIRE_ACTION [ ; Public anouncements are considered according to frequecy

        let value item st_english_proficiency english_proficiency
        if ((random 100) / 100) < value [
          set st_observation_pa 1
        ]
        if st_familiarity != 0 [
          if ((random 100) / 100) < value [
            set st_familiarity 1
          ]
        ]
      ]
    ]

    ;
    ; INTERNAL STATES
    ;
    set st_agent_location patch-here ; is something independet of the mind model, see the "do" function

    let sum_f 0
    ifelse _contagion_model = TRUE [
     set sum_f (W_inhibitingfeeling * st_desire_walkrand + st_observation_others_fear + W_decreasingfear * st_observation_staff_instr + W_decreasingfear * st_observation_pa + W_amplifyingfeeling * st_desire_evacuate)
    ]
    [
      set sum_f (W_inhibitingfeeling * st_desire_walkrand + W_decreasingfear * st_observation_staff_instr + W_decreasingfear * st_observation_pa + W_amplifyingfeeling * st_desire_evacuate)
    ]
    let first_exp_f 1 + exp (-1 * AL_STEEPNESS * (sum_f - AL_THRESHOLD))
    let second_exp_f exp (AL_STEEPNESS * AL_THRESHOLD)
    let third_exp_f 1 + exp (-1 * AL_STEEPNESS * AL_THRESHOLD)
    let alogistic_f ((1 / first_exp_f) - (1 / (1 + second_exp_f)) ) * third_exp_f
    let list_component []
    set list_component lput (W_persisting * st_fear) list_component
    set list_component lput alogistic_f list_component
    set st_fear max list_component


    let mult_component1 W_sensing_fire * st_observation_fire
    let mult_component2 W_persisting * st_belief_dangerous
    let mult_component3 W_sensing * st_observation_alarm
    let list_mult []
    set list_mult lput mult_component1 list_mult
    set list_mult lput mult_component2 list_mult
    set list_mult lput mult_component3 list_mult
    let sum_component (W_affectivebiasing * st_fear + st_observation_others_belief_dangerous) / (W_affectivebiasing + 1)
    set list_mult lput sum_component list_mult
    set st_belief_dangerous st_belief_dangerous + ETA_MENTAL * ((max list_mult) - st_belief_dangerous)

    ;set st_compliance
    ; compliance
    ;This is the row of the compliance table in the config file,
    let row 0                  ;children (st_age = 0) are at rows 0 and
    if st_age = 1 [set row 1]  ;adults   (st_age = 1) are at rows 1 and
    if st_age = 2 [set row 2]  ;eldery   (st_age = 2) are at rows 2
    let col 0
    if st_gender = 0 [set col 1]                 ; males are at columns 0 and female are at columns 1
    set st_compliance matrix:get compliance_level_matrix row col

    ; st_dead : is something independet of the mind model, see the "do" function
    ; st_fall? : is something independet of the mind model, see the "do" function


    let list_aux []
    set list_aux lput (W_inhibitingwalkrand * st_belief_dangerous)        list_aux
    set list_aux lput (W_inhibitingwalkrand * st_fear)                    list_aux
    set list_aux lput (W_inhibitingwalkrand * st_observation_staff_instr) list_aux
    set list_aux lput (W_inhibitingwalkrand * st_observation_pa)          list_aux
    set st_desire_walkrand st_desire_walkrand + (ETA_MENTAL * ((st_compliance * (1 - (max list_aux)) - st_desire_walkrand)))


    set list_aux []
    set list_aux lput (W_amplifyingevacuation * st_belief_dangerous)        list_aux
    set list_aux lput (W_amplifyingevacuation * st_fear)                    list_aux
    set list_aux lput (W_amplifyingevacuation * st_observation_staff_instr) list_aux
    set list_aux lput (W_amplifyingevacuation * st_observation_pa)          list_aux
    set st_desire_evacuate st_desire_evacuate + ETA_MENTAL * ((st_compliance * (max list_aux)) - st_desire_evacuate)


    ifelse st_fall = 1 [ set st_intention_evacuate 0]
    [ if st_desire_evacuate >= st_desire_walkrand [
        ; the desire of escape stems from contation, if it not observed fire yet.
        if st_observation_fire = 0 and statistics_hist_counted = 0 [
          let newval item ticks statistics_hist_contagion
          set statistics_hist_contagion replace-item ticks statistics_hist_contagion (newval + 1)
          set statistics_hist_counted 2 ; contagion = 2
        ]

        set st_intention_evacuate ETA_BODY * st_desire_evacuate
        if start_evacuate = 0 [ set start_evacuate ticks]
      ]
    ]

    ifelse st_fall = 1 [ set st_intention_walkrand 0]
    [ if st_desire_walkrand > st_desire_evacuate  [
        set st_intention_walkrand ETA_BODY * st_desire_walkrand
      ]
    ]
    ;nw
    if st_observation_pa = 1 and seconds = 0 [ ; Public anouncements are considered each 1 minute (seconds = 0).
      set st_desire_evacuate st_desire_evacuate * 1.1
      if st_desire_evacuate > 1 [
        set st_desire_evacuate 1
      ]
    ]


    ;
    ; ACTIONS
    ;
    set st_action_walkrandom st_intention_walkrand * speed
    set st_action_movetoexit st_intention_evacuate * speed * 3
  ]
end



;-----------------------------------------
;AUXILLIARY MODEL FUNCTIONS
;-----------------------------------------
;
;;;;;;;; auxiliar functions: environment and agent actions
;
to move-agent
  ;nw
  let stops_to_help? FALSE
  ask link-neighbors [                             ;this is the mechanism for when a group member falls: you do 'nothing'until this person stands up
    if st_fall = 1 [set stops_to_help? TRUE]
  ]
  if agent_to_help != nobody [                     ;this is the mechanism for when a non-group member falls that you want to help: when fallen, do nothing, when he/she stands up, you and your group members pick up the old speed
    ask agent_to_help [
      ifelse st_fall = 1 [set stops_to_help? TRUE] ; if the person still needs help, it continues stoped to help him.
        [
          set agent_to_help nobody                 ; if the person is already ok, he continues his path, and removes from his mind the intention to help that person.
          set speed speed_bkp
          ask link-neighbors [
            set speed speed_bkp
          ]
        ]
    ]
  ]
  if stops_to_help? = TRUE [stop]

  ; avoid passenger be stuck at same position between wall and fire
  ifelse count_time_stoped_same_position > 10 [
    ;show count_time_stoped_same_position
    set heading heading + 45

    if count_time_stoped_same_position > 15 [set heading heading + 135]
  ]
  [
    ;makes persons walk in every direction
    set heading (heading + 45 - (random 90))
  ]

  ; congestion speed factor
  let num_passengers_ahead 0
  let patches_ahead nobody
  ifelse st_intention_walkrand > st_intention_evacuate
  [ set patches_ahead patch-ahead  st_action_walkrandom]
  [ set patches_ahead patch-ahead  st_action_movetoexit]
  if patches_ahead != nobody [set num_passengers_ahead count agents-on patches_ahead]


  ; no more than 8 people in same patch
  if st_dead = 0 and breed != staff [

    ;df
    ; speed_factor to emulates physics: people cant walk through others, and they reduce the speed when are among many people.
    set congestion_speed_factor (1.05 - num_passengers_ahead /  8) ; Maximum is 8 people on one patch. if that is the case they dont move.
    if congestion_speed_factor <= 4  [set congestion_speed_factor 1]

    ;calls for speed of the passenger
    avoid-fire
    let back_step patch-here

    ;nw
    let group_speed_factor 1
    let max_speed_in_group speed
    let min_speed_in_group speed
    if st_leader = 1 and count link-neighbors > 0 [
      let l_max_speed_members link-neighbors with-max [speed]
      let l_min_speed_members link-neighbors with-min [speed]
      let smax [speed] of one-of l_max_speed_members
      if smax > max_speed_in_group [set max_speed_in_group smax]
      let smin [speed] of one-of l_min_speed_members
      if smin > max_speed_in_group [set min_speed_in_group smin]

      let new_speed min_speed_in_group + (max_speed_in_group - min_speed_in_group) * 0.4
      set speed     new_speed
    ]

    ifelse st_action_movetoexit > st_action_walkrandom and st_intention_evacuate > st_intention_walkrand and color = START_EVACUATE_COLOR
    [
      ifelse patch-at-heading-and-distance heading (st_action_movetoexit * congestion_speed_factor) = nobody
      [
        ifelse st_familiarity = 1
        [move-to nearest_exit_target ]
        [move-to main_entrance_target]
      ]
      [
        set current_speed st_action_movetoexit * congestion_speed_factor
        jump st_action_movetoexit * congestion_speed_factor
      ]
    ]
    [
      set current_speed st_action_walkrandom * congestion_speed_factor
      jump st_action_walkrandom * congestion_speed_factor
    ]


    ;nw if there are people linked to this guy, move them.
    let patch_of_leader patch-here
    ask link-neighbors [move-to patch_of_leader]


    ifelse [pcolor] of patch-here = FIRE_COLOR [
      move-to back_step
      set count_time_stoped_same_position count_time_stoped_same_position + 1
    ]
    [ set count_time_stoped_same_position 0]
    if start_evacuate > 0 [ move-to-exit ]
  ]
end

to move-staff  ; staff behavior ;nw
  set heading (heading + 45 - (random 90))
  let back_step patch-here
  jump 1
  if [pcolor] of patch-here = FIRE_COLOR [move-to back_step]
  if count patches in-radius PROTOCOL_DISTANCE with [pcolor = blue] <= 0 [move-to back_step]
  if sound_fire_alarm = 1 [ move-to-exit ]

  ; exit of staff
  ; staff: they left after all passengers have left ;df
  if count agents with [color != DEAD_PASSENGERS_COLOR] = 0 [
    if any? patches in-radius OBSERVATION_DISTANCE with [pcolor = EXIT_COLOR] [
      set heading towards one-of patches in-radius OBSERVATION_DISTANCE with [pcolor = EXIT_COLOR]
    ]
  ]
  if [pcolor] of patch-here = EXIT_COLOR and count agents with [color != DEAD_PASSENGERS_COLOR] = 0  [die]
end

to place-staff ; nw
  while [count staff < _number_staff_members] [
    foreach list_exits [
      let exit_patch nobody
      ask ? [set exit_patch one-of neighbors]

      create-staff 1 [
        set xcor [pxcor] of exit_patch
        set ycor [pycor] of exit_patch
        set color STAFF_COLOR
        set shape "person"
      ]

      if count staff >= _number_staff_members [stop]
    ]
  ]
end

to avoid-fire
  if any? patches in-cone 2 30 with [ pcolor = FIRE_COLOR ] [ ;nw
    ;red color and in the corner of the fire (number of red neighbors4 lower than 3).
    let p one-of patches with [ pcolor = FIRE_COLOR and count neighbors4 with [pcolor = red] <= 2 ]
    ;set heading towards p

    if p != nobody [
      let bkp_p patch-here
      move-to p
      ifelse patch-ahead  3 != nobody and [pcolor] of patch-ahead  3  != red [ fd  3 ]
      [
        ifelse patch-ahead -3 != nobody and [pcolor] of patch-ahead -3  != red [ fd -3 ] [move-to bkp_p]
      ]
   ]
  ]
end

to move-to-exit
  ; passengers
  if breed != staff and st_dead = 0 [

    set nearest_exit_target item 0 list_exits
    foreach list_exits [
      if ((distance ? ) < (distance nearest_exit_target)) [set nearest_exit_target ?]
    ]

    ;nw
    if [pcolor] of patch-here = EXIT_LIGHTING_COLOR or [pcolor] of neighbors = EXIT_LIGHTING_COLOR [set st_familiarity 1]
    if st_observation_staff_instr = 1 [set st_familiarity 1]

    ;nw
    let net_leader nearest_exit_target
    ask link-neighbors [set nearest_exit_target net_leader]


    let exit_heading 0
    ifelse st_familiarity = 1
    [set exit_heading  nearest_exit_target]
    [set exit_heading  main_entrance_target]
    if patch-here != exit_heading [set heading towards exit_heading]
  ]
end

to check-dead-by-fire ;nw
  ;when on FIRE_COLOR patch (=exit) 'die', means dissappear
  if [pcolor] of patch-here = FIRE_COLOR [
    set st_dead 1
    set color DEAD_PASSENGERS_COLOR ;passengers are DEAD_PASSENGERS_COLOR when die, but we can`t  see them in interface because they are below the fire
    ask link-neighbors [die] ; remove group links if they exist
  ]
end

to check-fall
 if _falls = TRUE [
   if (((st_action_movetoexit * congestion_speed_factor) > 3) and (count agents-here >= CROWD_CONGESTION_THRESHOLD)) ;nw
   [
     if random-float 100 < 0.5 [ ;nw
       set st_fall 1
       set speed 0
       set color FALL_COLOR
       set statistics_falls_total statistics_falls_total + 1
       set statistics_falls_average_per_passenger statistics_falls_total / (number_passengers - count agents with [color = DEAD_PASSENGERS_COLOR])
     ]
   ]

   ;nw
   if st_fall = 1 [
     ask link-neighbors [
       set speed 0
     ]
   ]
 ]
end

to-report get_social_identity [agent1 agent2] ;nw
  let culture1 [st_cultural_cluster] of agent1
  let culture2 [st_cultural_cluster] of agent2
  let links_agent1 nobody
  let agent1_linked_agent2 0
  ask agent1 [set links_agent1 link-neighbors]
  ask links_agent1 [ if who = [who] of agent2 [set agent1_linked_agent2 1]]

  let soc_id 0                                    ;nw social identity is a number either 0 or 1. 1 if the agents are from the same cultural cluster or if they are in the same group. 0 otherwise.
  if (culture1 = culture2) or (agent1_linked_agent2 = 1) [set soc_id 1]

  report soc_id
end

to check-decide-to-help ;nw
  if st_leader = 0 and st_group_member = 1 [stop]

  let list_agents_falled agents in-radius OBSERVATION_DISTANCE with [st_fall = 1 and color != DEAD_PASSENGERS_COLOR]
  let list_agents_around agents in-radius OBSERVATION_DISTANCE with [st_fall = 0]
  let num_agent_around count list_agents_around

  if count list_agents_falled > 0 and st_age != 0 [ ; only men, women, eldery help, children do not help (children follow the actions of the parent, do not decide themselves)
    let selected_fallen_person one-of list_agents_falled
    let social_identity get_social_identity self selected_fallen_person

    let row 0                                    ; This is the row of the helping table in the config file,
    if st_gender = 0 [set row 4]                 ; males are at rows 0 to 3 and women are at rows 4 to 7.
    if social_identity = 0 [set row row + 2]     ; social_identity = 1 are at rows 0-1 (males) and 4-5(females)
    if st_age = 2 [set row row + 1]              ;adults (st_age = 1) are at rows 0 and 2 (males) and rows 4 and 6 (females)
    let col 0
    if st_gender = 0 [set col 3]                 ; males are at columns 0 to 2 and women are at columns 3 to 5.
    if st_age = 1    [set col col + 1]           ;adults (st_age = 1) are at colum 1 (males) and colum 4 (females)
    if st_age = 2    [set col col + 2]           ;eldery (st_age = 2) are at colum 2 (males) and colum 5 (females)

    let helping_chance matrix:get helping_chance_matrix row col

    if (random 100 < helping_chance) [
      move-to [patch-here] of selected_fallen_person
      set agent_to_help selected_fallen_person
      set speed 0
      ask link-neighbors [set speed 0]
    ]
  ]
end

to check-get-up
  if ( color = FALL_COLOR ) [
    ifelse ticks-since-fall = 30
      [ set color FALL_COLOR + 1]
      [ set ticks-since-fall ticks-since-fall + 1
        stop ]
  ]

  if ticks - ticks-since-fall > 30 [
    set ticks-since-fall 0
    set speed speed_bkp ; after getup, it is back the original speed of this agent
    set st_fall 0

    ;nw
    if st_fall = 1 [
      ask link-neighbors [
        set speed speed_bkp
      ]
    ]
    ;nw
    set color PASSENGERS_COLOR
  ]
end


to check-exit
  ; exit of passengers
  let escape_rate 1;df

  ;nw
  let num_people_door1 agents with [is-patch? nearest_exit_target and start_evacuate > 0 and breed != staff and [pcolor] of patch-here = EXIT_COLOR and pxcor < (min-pxcor + 3) and ((st_familiarity = 1 and [pxcor] of nearest_exit_target < (min-pxcor + 3)) or st_familiarity = 0)]
  let num_people_door2 agents with [is-patch? nearest_exit_target and start_evacuate > 0 and breed != staff and [pcolor] of patch-here = EXIT_COLOR and pxcor > (max-pxcor - 3) and ((st_familiarity = 1 and [pxcor] of nearest_exit_target > (min-pxcor + 3)) or st_familiarity = 0)]
  let num_people_door3 agents with [is-patch? nearest_exit_target and start_evacuate > 0 and breed != staff and [pcolor] of patch-here = EXIT_COLOR and pycor < (min-pycor + 3) and ((st_familiarity = 1 and [pycor] of nearest_exit_target < (min-pycor + 3)) or st_familiarity = 0)]
  let num_people_door4 agents with [is-patch? nearest_exit_target and start_evacuate > 0 and breed != staff and [pcolor] of patch-here = EXIT_COLOR and pycor > (max-pycor - 3) and ((st_familiarity = 1 and [pycor] of nearest_exit_target > (max-pycor - 3)) or st_familiarity = 0)]

  if count num_people_door1 <= 5 [ ask num_people_door1 [
      if statistics_hist_counted = 2 [
        set statistics_average_resp_time_from_contagion_died statistics_average_resp_time_from_contagion_died + start_evacuate - start_place_fire
        set divisor_after_contagion divisor_after_contagion + 1
      ]
      if statistics_hist_counted = 1 [
        set statistics_average_resp_time_from_observation_fire_died statistics_average_resp_time_from_observation_fire_died + start_evacuate - start_observation_fire
        set divisor_after_observation_fire divisor_after_observation_fire + 1
      ]
      if statistics_hist_counted = 3 [
        set divisor_after_fire_alarm divisor_after_fire_alarm + 1
        ;set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_fire_alarm
        set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_place_fire
      ]

      set statistics_average_resp_time_from_start_fire_cumulative      statistics_average_resp_time_from_start_fire_cumulative      + (ticks - start_place_fire); nw
      set statistics_average_resp_time_from_decide_evacuate_cumulative statistics_average_resp_time_from_decide_evacuate_cumulative + (ticks - start_evacuate) ;nw
      set statistics_evacuated_door1 statistics_evacuated_door1 + 1
      die
    ]
  ]
  if count num_people_door1  > 5 [ ask n-of (5 + escape_rate) num_people_door1 [
      if statistics_hist_counted = 2 [
        set statistics_average_resp_time_from_contagion_died statistics_average_resp_time_from_contagion_died + start_evacuate - start_place_fire
        set divisor_after_contagion divisor_after_contagion + 1
      ]
      if statistics_hist_counted = 1 [
        set statistics_average_resp_time_from_observation_fire_died statistics_average_resp_time_from_observation_fire_died + start_evacuate - start_observation_fire
        set divisor_after_observation_fire divisor_after_observation_fire + 1
      ]
      if statistics_hist_counted = 3 [
        set divisor_after_fire_alarm divisor_after_fire_alarm + 1
        set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_place_fire
      ]

      set statistics_average_resp_time_from_start_fire_cumulative      statistics_average_resp_time_from_start_fire_cumulative      + (ticks - start_place_fire); nw
      set statistics_average_resp_time_from_decide_evacuate_cumulative statistics_average_resp_time_from_decide_evacuate_cumulative + (ticks - start_evacuate) ;nw
      set statistics_evacuated_door1 statistics_evacuated_door1 + 1
      die
    ]
  ]

  if count num_people_door2 <= 5 [ask num_people_door2 [
      if statistics_hist_counted = 2 [
        set statistics_average_resp_time_from_contagion_died statistics_average_resp_time_from_contagion_died + start_evacuate - start_place_fire
        set divisor_after_contagion divisor_after_contagion + 1
      ]
      if statistics_hist_counted = 1 [
        set statistics_average_resp_time_from_observation_fire_died statistics_average_resp_time_from_observation_fire_died + start_evacuate - start_observation_fire
        set divisor_after_observation_fire divisor_after_observation_fire + 1
      ]
      if statistics_hist_counted = 3 [
        set divisor_after_fire_alarm divisor_after_fire_alarm + 1
        ;set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_fire_alarm
        set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_place_fire
      ]

      set statistics_average_resp_time_from_start_fire_cumulative      statistics_average_resp_time_from_start_fire_cumulative      + (ticks - start_place_fire); nw
      set statistics_average_resp_time_from_decide_evacuate_cumulative statistics_average_resp_time_from_decide_evacuate_cumulative + (ticks - start_evacuate) ;nw
      set statistics_evacuated_door2 statistics_evacuated_door2 + 1
      die
    ]
  ]
  if count num_people_door2  > 5 [ask n-of (5 + escape_rate) num_people_door2 [
      if statistics_hist_counted = 2 [
        set statistics_average_resp_time_from_contagion_died statistics_average_resp_time_from_contagion_died + start_evacuate - start_place_fire
        set divisor_after_contagion divisor_after_contagion + 1
      ]
      if statistics_hist_counted = 1 [
        set statistics_average_resp_time_from_observation_fire_died statistics_average_resp_time_from_observation_fire_died + start_evacuate - start_observation_fire
        set divisor_after_observation_fire divisor_after_observation_fire + 1
      ]
      if statistics_hist_counted = 3 [
        set divisor_after_fire_alarm divisor_after_fire_alarm + 1
        ;set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_fire_alarm
        set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_place_fire
      ]

      set statistics_average_resp_time_from_start_fire_cumulative      statistics_average_resp_time_from_start_fire_cumulative      + (ticks - start_place_fire); nw
      set statistics_average_resp_time_from_decide_evacuate_cumulative statistics_average_resp_time_from_decide_evacuate_cumulative + (ticks - start_evacuate) ;nw
      set statistics_evacuated_door2 statistics_evacuated_door2 + 1
      die
    ]
  ]

  if count num_people_door3 <= 5 [ask num_people_door3 [
      if statistics_hist_counted = 2 [
        set statistics_average_resp_time_from_contagion_died statistics_average_resp_time_from_contagion_died + start_evacuate - start_place_fire
        set divisor_after_contagion divisor_after_contagion + 1
      ]
      if statistics_hist_counted = 1 [
        set statistics_average_resp_time_from_observation_fire_died statistics_average_resp_time_from_observation_fire_died + start_evacuate - start_observation_fire
        set divisor_after_observation_fire divisor_after_observation_fire + 1
      ]
      if statistics_hist_counted = 3 [
        set divisor_after_fire_alarm divisor_after_fire_alarm + 1
        ;set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_fire_alarm
        set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_place_fire
      ]

      set statistics_average_resp_time_from_start_fire_cumulative      statistics_average_resp_time_from_start_fire_cumulative      + (ticks - start_place_fire); nw
      set statistics_average_resp_time_from_decide_evacuate_cumulative statistics_average_resp_time_from_decide_evacuate_cumulative + (ticks - start_evacuate) ;nw
      set statistics_evacuated_door3 statistics_evacuated_door3 + 1
      die
    ]
  ]
  if count num_people_door3  > 5 [ask n-of (5 + escape_rate) num_people_door3 [
      if statistics_hist_counted = 2 [
        set statistics_average_resp_time_from_contagion_died statistics_average_resp_time_from_contagion_died + start_evacuate - start_place_fire
        set divisor_after_contagion divisor_after_contagion + 1
      ]
      if statistics_hist_counted = 1 [
        set statistics_average_resp_time_from_observation_fire_died statistics_average_resp_time_from_observation_fire_died + start_evacuate - start_observation_fire
        set divisor_after_observation_fire divisor_after_observation_fire + 1
      ]
      if statistics_hist_counted = 3 [
        set divisor_after_fire_alarm divisor_after_fire_alarm + 1
        ;set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_fire_alarm
        set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_place_fire
      ]

      set statistics_average_resp_time_from_start_fire_cumulative      statistics_average_resp_time_from_start_fire_cumulative      + (ticks - start_place_fire); nw
      set statistics_average_resp_time_from_decide_evacuate_cumulative statistics_average_resp_time_from_decide_evacuate_cumulative + (ticks - start_evacuate) ;nw
      set statistics_evacuated_door3 statistics_evacuated_door3 + 1
      die
    ]
  ]

  if count num_people_door4 <= 5 [ask num_people_door4 [
      if statistics_hist_counted = 2 [
        set statistics_average_resp_time_from_contagion_died statistics_average_resp_time_from_contagion_died + start_evacuate - start_place_fire
        set divisor_after_contagion divisor_after_contagion + 1
      ]
      if statistics_hist_counted = 1 [
        set statistics_average_resp_time_from_observation_fire_died statistics_average_resp_time_from_observation_fire_died + start_evacuate - start_observation_fire
        set divisor_after_observation_fire divisor_after_observation_fire + 1
      ]
      if statistics_hist_counted = 3 [
        set divisor_after_fire_alarm divisor_after_fire_alarm + 1
        ;set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_fire_alarm
        set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_place_fire
      ]

      set statistics_average_resp_time_from_start_fire_cumulative      statistics_average_resp_time_from_start_fire_cumulative      + (ticks - start_place_fire); nw
      set statistics_average_resp_time_from_decide_evacuate_cumulative statistics_average_resp_time_from_decide_evacuate_cumulative + (ticks - start_evacuate) ;nw
      set statistics_evacuated_door4 statistics_evacuated_door4 + 1
      die
    ]
  ]
  if count num_people_door4  > 5 [ask n-of (5 + escape_rate) num_people_door4 [
      if statistics_hist_counted = 2 [
        set statistics_average_resp_time_from_contagion_died statistics_average_resp_time_from_contagion_died + start_evacuate - start_place_fire
        set divisor_after_contagion divisor_after_contagion + 1
      ]
      if statistics_hist_counted = 1 [
        set statistics_average_resp_time_from_observation_fire_died statistics_average_resp_time_from_observation_fire_died + start_evacuate - start_observation_fire
        set divisor_after_observation_fire divisor_after_observation_fire + 1
      ]
      if statistics_hist_counted = 3 [
        set divisor_after_fire_alarm divisor_after_fire_alarm + 1
        ;set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_fire_alarm
        set statistics_average_resp_time_from_fire_alarm_died statistics_average_resp_time_from_fire_alarm_died + start_evacuate - start_place_fire
      ]

      set statistics_average_resp_time_from_start_fire_cumulative      statistics_average_resp_time_from_start_fire_cumulative      + (ticks - start_place_fire); nw
      set statistics_average_resp_time_from_decide_evacuate_cumulative statistics_average_resp_time_from_decide_evacuate_cumulative + (ticks - start_evacuate) ;nw
      set statistics_evacuated_door4 statistics_evacuated_door4 + 1
      die
    ]
  ]
end

to express
  set st_express_fear st_fear
  set st_express_belief_dangerous st_belief_dangerous
end



;-----------------------------------------
;GENERAL AUXILLIARY FUNCTIONS
;-----------------------------------------
;nw
to set-time
  ifelse ticks = 0
  [
    set days 1
    set hours 0
    set minutes 0
    set seconds 0
  ]
  [
    set seconds seconds + 1   ;df change this place.
    set pa_count_seconds pa_count_seconds + 1
    set alarm_count_seconds alarm_count_seconds + 1
    if seconds > 59 [
      set seconds 0
      set minutes minutes + 1
    ]
    if minutes > 59 [
      set minutes 0
      set hours hours + 1
      if hours > 23 [
        set hours 0
        set days days + 1
      ]
    ]
  ]
  let hours_string (word hours)
  let minutes_string (word minutes)
  let seconds_string (word seconds)
  if seconds < 10 [
    set seconds_string (word "0" seconds)
  ]
  if minutes < 10 [
    set minutes_string (word "0" minutes)
  ]
  if hours < 10 [
    set hours_string (word "0" hours)
  ]
  set current_time (word hours_string ":" minutes_string ":" seconds_string)
end



;-----------------------------------------
;INTERFACE FUNCTIONS
;-----------------------------------------
to place-obstacle
  if pxcor < 3 and pxcor > -3 and pycor < 3 and pycor > -3 [set pcolor  FIRE_COLOR]
end

to place-fire ;nw
  if start_place_fire = 0 [set start_place_fire ticks]

  ;0 = no fire in the room but with dangerous situation, 1 = random, 2 = centre, 3 = in front of main door, 4 = in front of another door, not the main., 5 = in a corner.
  let x 0
  let y 0

  ;random
  if PLACE_FIRE_POSITION = 1 [
    set x (random max-pxcor * 2) - random max-pxcor ;; in order to generate negative numbers, if max-pxcor = 15: generate numbers between 0 and 29 and subtract 15 so our range is between -14 and +14
    set y (random max-pycor * 2) - random max-pycor ;; same logic for y.
                                                    ;; try new coordinates while one of the two forbiden conditions matches.
                                                    ;; while x and y overlap the left exit of the room  OR
                                                    ;; while x and y overlap the rigth side of the room
    while [ x <= (min-pxcor + 4) or x >= (max-pxcor - 4) or y <= (min-pycor + 4) or y >= (max-pycor - 4)] [
      set x random max-pxcor
      set y random max-pycor
    ]
  ]

  ; centre
  if PLACE_FIRE_POSITION = 2 [
      set x 0
      set y 0
  ]

  ; in front of the main door OR another door
  if PLACE_FIRE_POSITION = 3 or PLACE_FIRE_POSITION = 4 [
    let door main_entrance_target ; assume 3 and change it if is the option 4.
    if PLACE_FIRE_POSITION = 4 [
      let r 0
      while [r = 0] [set r random length list_exits]
      set door item r list_exits
    ]
    set x [pxcor] of door
    set y [pycor] of door
    if x = min-pxcor and y != min-pycor and y != min-pycor [set x x + 4] ; left
    if x = max-pxcor and y != min-pycor and y != min-pycor [set x x - 4] ; right
    if y = min-pycor and x != min-pxcor and x != min-pxcor [set y y + 4] ; down
    if y = max-pycor and x != min-pxcor and x != min-pxcor [set y y - 4] ; up
  ]

  ; in a corner
  if PLACE_FIRE_POSITION = 5 [
    let op random 4
    if op = 0 [set x min-pxcor + 2 set y min-pycor + 2]
    if op = 1 [set x min-pxcor + 2 set y max-pycor - 2]
    if op = 2 [set x max-pxcor - 2 set y min-pycor + 2]
    if op = 3 [set x max-pxcor - 2 set y max-pycor - 2]
  ]


  if PLACE_FIRE_POSITION != 0 [
    ask patches with [ pxcor < FIRE_RADIUS + x and pxcor > ( -1 * FIRE_RADIUS) + x and pycor < FIRE_RADIUS + y and pycor > ( -1 * FIRE_RADIUS) + y ] [set pcolor  FIRE_COLOR]
  ]

  set place_fire_tick ticks
end

to check-fire-alarm
  ifelse _fire_alarm = TRUE
  [
    set sound_fire_alarm 1
    if start_fire_alarm = 0 [set start_fire_alarm ticks]
  ]
  [ set sound_fire_alarm 0 ]
end

to check-public-announcement
  ifelSe _public_announcement = TRUE
  [ set sound_public_announcement 1 ]
  [ set sound_public_announcement 0 ]
end



;-----------------------------------------
;PLOTS
;-----------------------------------------
to do-plots
  if count agents > 0 [
    ; graph with all signals from agent X
    if is-agent? agent 0 [
      ask agent 0 [
        ;    set g_st_others_belief_dangerous             st_others_belief_dangerous
        ;    set g_st_others_fear                         st_others_fear

        ;    set g_st_observation_fire                    st_observation_fire
        ;    set g_st_observation_alarm                   st_observation_alarm
        ;    set g_st_observation_others_belief_dangerous st_observation_others_belief_dangerous
        ;    set g_st_observation_others_fear             st_observation_others_fear
        ;    set g_st_observation_staff_instr             st_observation_staff_instr
        ;    set g_st_observation_pa                      st_observation_pa

        ;    set g_st_agent_location                      st_agent_location
        ;    set g_st_fear                                st_fear

        ;    set g_st_belief_dangerous                    st_belief_dangerous
        ;    set g_st_compliance                          st_compliance

        ;    set g_st_dead                                st_dead
        ;    set g_st_fall                                st_fall
        ;    set g_st_desire_walkrand                     st_desire_walkrand
        ;    set g_st_desire_evacuate                     st_desire_evacuate

        set g_st_intention_walkrand                  st_intention_walkrand
        set g_st_intention_evacuate                  st_intention_evacuate
        ;    set g_st_familiarity                         st_familiarity

        ;    set g_st_express_belief_dangerous            st_express_belief_dangerous
        ;    set g_st_express_fear                        st_express_fear
        ;    set g_st_action_walkrandom                   st_action_walkrandom
        ;    set g_st_action_movetoexit                   st_action_movetoexit
      ]
    ]

  set-current-plot "Evacuation1"
  ;set-current-plot-pen "Survivors"
  ;plot count agents
  set-current-plot-pen "Evacuated"
  plot number_passengers - count agents + 1

  set-current-plot "Evacuation2"
  set-current-plot-pen "dead"
  plot count agents with [ st_dead = 1 ]
  set-current-plot-pen "fallen"
  plot count agents with [ st_fall = 1 ]
  set-current-plot-pen "fallen_total"
  plot statistics_falls_total

  let divisor 0
  let agents_died_by_fire agents with [color = DEAD_PASSENGERS_COLOR]
  set divisor count agents - count agents_died_by_fire
  if divisor = 0 [set divisor 1]

  let sum_tmp 0
  ask agents [ set sum_tmp sum_tmp + st_fear]
  set statistics_average_fear sum_tmp / divisor

  set sum_tmp 0
  ask agents [ set sum_tmp sum_tmp + st_belief_dangerous]
  set statistics_average_belief_dangerous sum_tmp / divisor

  set sum_tmp 0
  ask agents [ set sum_tmp sum_tmp + st_intention_evacuate]
  set statistics_average_intention_evacuate sum_tmp / divisor

  set sum_tmp 0
  ask agents [ set sum_tmp  sum_tmp + st_intention_walkrand]
  set statistics_average_intention_walkrand sum_tmp / divisor

  set sum_tmp 0
  ask agents [ set sum_tmp  sum_tmp + st_desire_evacuate]
  set statistics_average_desire_evacuate sum_tmp / divisor

  set sum_tmp 0
  ask agents [ set sum_tmp  sum_tmp + st_desire_walkrand]
  set statistics_average_desire_walkrand sum_tmp / divisor

  ;check if correct, newly added for speed
  set sum_tmp 0
  ask agents [ set sum_tmp sum_tmp + st_action_walkrandom]
  set statistics_average_walking_speed sum_tmp / count agents

  set sum_tmp []
  ask agents [ set sum_tmp lput st_action_walkrandom sum_tmp]
  set statistics_maximum_walking_speed max sum_tmp
  set statistics_minimum_walking_speed min sum_tmp


  set sum_tmp 0
  ask agents [ set sum_tmp sum_tmp + st_action_movetoexit]
  set statistics_average_running_speed sum_tmp / count agents

  set sum_tmp []
  ask agents [ set sum_tmp lput st_action_movetoexit sum_tmp]
  set statistics_maximum_running_speed max sum_tmp
  set statistics_minimum_running_speed min sum_tmp

  ; evacuation average time of who saw the fire
  set sum_tmp 0
  set divisor 0
  ask agents [
    if statistics_hist_counted = 1 [
      set divisor divisor + 1
      set sum_tmp  sum_tmp + (start_evacuate - start_place_fire)
    ]
  ]
  if divisor = 0 [set divisor 1]
  set statistics_average_resp_time_from_observation_fire (sum_tmp + statistics_average_resp_time_from_observation_fire_died) / (divisor + divisor_after_observation_fire)

  ; evacuation average time of who was contegion
  set sum_tmp 0
  set divisor 0
  ask agents [
    if statistics_hist_counted = 2 [
      set divisor divisor + 1
      set sum_tmp  sum_tmp + (start_evacuate - start_place_fire)
    ]
  ]
  if divisor = 0 [set divisor 1]
  set statistics_average_resp_time_from_contagion (sum_tmp + statistics_average_resp_time_from_contagion_died) / (divisor + divisor_after_contagion)

  ; evacuation average time of who heard the alarm
  set sum_tmp 0
  set divisor 0
  ask agents [
    if statistics_hist_counted = 3 and start_evacuate > start_place_fire [
      set divisor divisor + 1
      set sum_tmp  sum_tmp + (start_evacuate - start_place_fire)
    ]
  ]
  if divisor = 0 [set divisor 1]
  set statistics_average_resp_time_from_fire_alarm (sum_tmp + statistics_average_resp_time_from_fire_alarm_died) / (divisor + divisor_after_fire_alarm)
]
end
@#$#@#$#@
GRAPHICS-WINDOW
395
10
1389
545
20
10
24.0
1
10
1
1
1
0
0
0
1
-20
20
-10
10
1
1
1
ticks
30.0

BUTTON
1
168
67
201
NIL
setup
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
69
168
132
201
NIL
go
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
0
10
395
43
number_passengers
number_passengers
1
6743
799
1
1
NIL
HORIZONTAL

PLOT
1
556
312
793
Evacuation1
time (seconds)
state of passengers
0.0
10.0
0.0
10.0
true
true
"" ""
PENS
"turtles present" 1.0 0 -16777216 true "" "plot count turtles"
"evacuated" 1.0 0 -2674135 true "" ""

BUTTON
69
203
133
236
NIL
place-fire
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SWITCH
163
84
273
117
_fire_alarm
_fire_alarm
0
1
-1000

SWITCH
-1
116
164
149
_public_announcement
_public_announcement
0
1
-1000

SLIDER
0
42
395
75
_number_staff_members
_number_staff_members
0
100
0
1
1
NIL
HORIZONTAL

PLOT
316
556
679
799
average fear
time (seconds)
level of fear
0.0
1.0
0.0
1.0
true
false
"" ""
PENS
"plot_fear" 1.0 0 -16777216 true "" "plot statistics_average_fear"

PLOT
688
558
1027
798
average belief dangerous
time (seconds)
intensity belief dangerous
0.0
10.0
0.0
1.0
true
false
"" ""
PENS
"plot_belief_dangerous" 1.0 0 -16777216 true "" "plot statistics_average_belief_dangerous"

PLOT
1673
215
1930
424
average intention evacuate
time (seconds)
intensity intention to evacuate
0.0
10.0
0.0
1.0
true
false
"" ""
PENS
"plot intention evacuate" 1.0 0 -16777216 true "" "plot statistics_average_intention_evacuate"

PLOT
1413
215
1673
424
average intention walkrand
time (seconds)
intensity intention walk randomly
0.0
10.0
0.0
1.0
true
false
"" ""
PENS
"plot_intention_walkrand" 1.0 0 -16777216 true "" "plot statistics_average_intention_walkrand"

PLOT
1413
428
2258
850
plot model
time
value
0.0
10.0
-1.0
1.0
false
true
"" ""
PENS
"g_st_others_belief_dangerous" 1.0 0 -7500403 true "" "plot g_st_others_belief_dangerous"
"g_st_others_fear" 1.0 0 -2674135 true "" "plot g_st_others_fear"
"g_st_observation_fire" 1.0 0 -955883 true "" "plot g_st_observation_fire"
"g_st_observation_alarm" 1.0 0 -6459832 true "" "plot g_st_observation_alarm"
"g_st_observation_others_belief_dangerous" 1.0 0 -1184463 true "" "plot g_st_observation_others_belief_dangerous"
"g_st_observation_others_fear" 1.0 0 -10899396 true "" "plot g_st_observation_others_fear"
"g_st_observation_staff_instr " 1.0 0 -13840069 true "" "plot g_st_observation_staff_instr"
"g_st_observation_pa" 1.0 0 -14835848 true "" "plot g_st_observation_pa"
"g_st_fear" 1.0 0 -13791810 true "" "plot g_st_fear"
"g_st_belief_dangerous" 1.0 0 -13345367 true "" "plot g_st_belief_dangerous"
"g_st_compliance" 1.0 0 -8630108 true "" "plot g_st_compliance"
"g_st_dead" 1.0 0 -5825686 true "" "plot g_st_dead"
"g_st_fall" 1.0 0 -2064490 true "" "plot g_st_fall"
"g_st_desire_walkrand" 1.0 0 -16777216 true "" "plot g_st_desire_walkrand"
"g_st_desire_evacuate" 1.0 0 -1069655 true "" "plot g_st_desire_evacuate"
"g_st_intention_walkrand" 1.0 0 -408670 true "" "plot g_st_intention_walkrand"
"g_st_intention_evacuate" 1.0 0 -4399183 true "" "plot g_st_intention_evacuate"
"g_st_familiarity" 1.0 0 -5516827 true "" "plot g_st_familiarity"
"g_st_express_belief_dangerous" 1.0 0 -3425830 true "" "plot g_st_express_belief_dangerous"
"g_st_express_fear" 1.0 0 -10603201 true "" "plot g_st_express_fear"
"g_st_action_walkrandom" 1.0 0 -15390905 true "" "plot g_st_action_walkrandom"
"g_st_action_movetoexit" 1.0 0 -14333415 true "" "plot g_st_action_movetoexit"

BUTTON
0
202
67
235
NIL
place-staff
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

PLOT
1673
15
1930
213
average desire evacuate
time (seconds)
intensity desire to evacuate
0.0
10.0
0.0
1.0
true
false
"" ""
PENS
"default" 1.0 0 -16777216 true "" "plot statistics_average_desire_evacuate"

PLOT
1413
15
1673
213
desire walkrand
time (seconds)
intensity desire walk randomly
0.0
10.0
0.0
1.0
true
false
"" ""
PENS
"default" 1.0 0 -16777216 true "" "plot statistics_average_desire_walkrand"

SWITCH
-1
84
164
117
_contagion_model
_contagion_model
0
1
-1000

SLIDER
163
199
390
232
_percentage_familiarity
_percentage_familiarity
0
100
50
1
1
NIL
HORIZONTAL

PLOT
1932
15
2256
214
average response time
time (seconds)
response time
0.0
10.0
0.0
10.0
true
true
"" ""
PENS
"resp_time_observation" 1.0 0 -5298144 true "" "plot statistics_average_resp_time_from_observation_fire"
"resp_time_contagion" 1.0 0 -14070903 true "" "plot statistics_average_resp_time_from_contagion"
"resp_time_fire_alarm" 1.0 0 -7500403 true "" "plot statistics_average_resp_time_from_fire_alarm"
"fire_event" 1.0 0 -12186836 true "" ""
"fire_alarm_event" 1.0 0 -12895429 true "" ""

PLOT
0
793
312
1024
Evacuation2
state of passengers
evacuation (seconds)
0.0
10.0
0.0
10.0
true
true
"" ""
PENS
"fallen" 1.0 0 -955883 true "" ""
"fallen_total" 1.0 0 -7858858 true "" ""
"dead" 1.0 0 -7500403 true "" ""

PLOT
1932
215
2256
424
Histrogram: start evacuation cause
time slices
number of passengers
0.0
250.0
0.0
500.0
true
true
"" ""
PENS
"observe_fire" 5.0 1 -13345367 true "" "histogram statistics_hist_observeFire"
"contagion" 5.0 1 -2064490 true "" "histogram statistics_hist_contagion"
"fire_alarm" 5.0 1 -13840069 true "" "histogram statistics_hist_fireAlarm"

SWITCH
273
84
363
117
_falls
_falls
0
1
-1000

PLOT
1029
558
1409
799
Average speed
time
speed (m/s)
0.0
500.0
0.0
1.0
true
true
"" ""
PENS
"walking" 1.0 0 -16777216 true "" "plot statistics_average_walking_speed"
"running" 1.0 0 -7500403 true "" "plot statistics_average_running_speed"
"max walking" 1.0 0 -2674135 true "" "plot statistics_maximum_walking_speed"
"min walking" 1.0 0 -955883 true "" "plot statistics_minimum_walking_speed"
"max running" 1.0 0 -6459832 true "" "plot statistics_maximum_running_speed"
"min running" 1.0 0 -1184463 true "" "plot statistics_minimum_running_speed"

MONITOR
319
828
439
873
evacuated door 1
statistics_evacuated_door1
17
1
11

MONITOR
442
829
562
874
evacuated door 2
statistics_evacuated_door2
17
1
11

MONITOR
563
829
683
874
evacuated door 3
statistics_evacuated_door3
17
1
11

MONITOR
686
829
806
874
evacuated door 4
statistics_evacuated_door4
17
1
11

MONITOR
812
829
964
874
number of people died
count turtles with [color = grey]
17
1
11

PLOT
318
878
518
1028
Flowrate  of egress door 1
Time (sec)
Flowrate (people per meter per second)
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"default" 1.0 0 -16777216 true "" "plot statistics_evacuated_door1 / (ticks + 1)"

PLOT
520
878
720
1028
Flowrate  of egress door 2
Time (sec)
Flowrate (people per meter per second)
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"default" 1.0 0 -16777216 true "" "plot statistics_evacuated_door2 / (ticks + 1)"

PLOT
725
878
925
1028
Flowrate  of egress door 3
Time (sec)
Flowrate (people per meter per second)
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"default" 1.0 0 -16777216 true "" "plot statistics_evacuated_door3 / (ticks + 1)"

PLOT
928
878
1128
1028
Flowrate  of egress door 4
Time (sec)
Flowrate (people per meter per second)
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"default" 1.0 0 -16777216 true "" "plot statistics_evacuated_door4 / (ticks + 1)"

PLOT
1128
823
1411
1026
Average flowrate of egress through all doors
Time (sec)
Flowrate (people per meter per second)
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"default" 1.0 0 -16777216 true "" "plot (statistics_evacuated_door1 + statistics_evacuated_door2 + statistics_evacuated_door3 + statistics_evacuated_door4 )/ ((ticks + 1) * 4)"

SLIDER
163
168
390
201
_percentage_females
_percentage_females
0
100
50
1
1
NIL
HORIZONTAL

SLIDER
163
232
390
265
_percentage_children
_percentage_children
0
50
15
1
1
NIL
HORIZONTAL

INPUTBOX
63
328
172
388
_groups_of_2_ratio
33
1
0
Number

INPUTBOX
172
328
281
388
_groups_of_3_ratio
33
1
0
Number

INPUTBOX
281
328
390
388
_groups_of_4_ratio
34
1
0
Number

SLIDER
163
295
390
328
_percentage_people_traveling_alone
_percentage_people_traveling_alone
0
100
50
1
1
NIL
HORIZONTAL

MONITOR
-1
235
133
308
TIME
current_time
17
1
18

SWITCH
273
116
363
149
_help
_help
1
1
-1000

SLIDER
163
264
390
297
_percentage_eldery
_percentage_eldery
0
100
15
1
1
NIL
HORIZONTAL

SWITCH
163
116
273
149
_exit_lighting
_exit_lighting
1
1
-1000

INPUTBOX
260
394
389
454
room_environment_type
6
1
0
Number

INPUTBOX
128
394
260
454
PLACE_FIRE_POSITION
1
1
0
Number

INPUTBOX
128
453
389
513
setting_cultural_cluster_distribution
1
1
0
Number

@#$#@#$#@
## WHAT IS IT?
  This is a model that simulates people evacuating a building, due to an incident (red square).


## HOW IT WORKS
  The model is divided in the physical world and agents. Agents have their own characteristics, some of them are configurable and others are part of the model. Agents start in black and when an agent decides to evacuate it becomes pink. If it falls in the environment it turns orange for a certain time defined in the model.
  Some agents are green, they are staff members that help others to evacuate. If a staff agent is in the vision radius of another agent that wants to evacuate, this last agent will follow the "instructions" of the staff, what means: evacuate through the nearest exit. Grey agents are dead by an event (fire/explosion/etc.) that initiates the evacuation process.
  The world follow the same pattern. Some characteristics are easily changeble, others are fixed or need to be changed in code. There are pre-build scenarios that could be imported.
  The simulation runs until every alive agent evacuates the scenario taking the blue exits.


## HOW TO USE IT
  1. Adjust the Controls according to the desired scenario;
  2. Press button SETUP (at this point the configurations will be loaded).
  3. Press button GO to run the simulation.
  4. The simulation stops automatically when finished (all alive agents have evacuated).


## THINGS TO NOTICE
For explanation of the interface configuration and other configurations see the file config.nls.


## THINGS TO TRY
  Try different combinations and observe the results (evacuation time, number of falls, wich exits the agents take, when they start to evacuate, etc).
Tuning of the model: there are parameters that define the internal behavior/reaction of the agents. You can find them in config.nls


## EXTENDING THE MODEL
  You can change the model in the main code:
  - add or remove things of the agents (find ;Model) or in the environment and interactions between agents and environment (spread in the code).
  - you can import a new building layout or draw a new environment
  - create with obstackes in the environment


## CREDITS AND REFERENCES

Natalie Van der Wal and Daniel Formolo
Vrije Universiteit Amsterdam

This research was undertaken as part of the EU HORIZON 2020 Project IMPACT (GA 653383) and Science without Borders – CNPq (scholarship reference:  235134/2014-7). We would like to thank our Consortium Partners and stakeholders for their input and the Brazilian Government.
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

container
false
0
Rectangle -7500403 false false 0 75 300 225
Rectangle -7500403 true true 0 75 300 225
Line -16777216 false 0 210 300 210
Line -16777216 false 0 90 300 90
Line -16777216 false 150 90 150 210
Line -16777216 false 120 90 120 210
Line -16777216 false 90 90 90 210
Line -16777216 false 240 90 240 210
Line -16777216 false 270 90 270 210
Line -16777216 false 30 90 30 210
Line -16777216 false 60 90 60 210
Line -16777216 false 210 90 210 210
Line -16777216 false 180 90 180 210

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

rails
true
0
Rectangle -7500403 true true 0 0 300 300
Line -1 false 285 0 285 300
Line -1 false 255 0 255 300
Line -1 false 225 0 225 300
Line -1 false 180 0 180 300
Line -1 false 135 0 135 300
Line -1 false 105 0 105 300
Line -1 false 75 0 75 300
Line -1 false 30 0 30 300

sheep
false
15
Circle -1 true true 203 65 88
Circle -1 true true 70 65 162
Circle -1 true true 150 105 120
Polygon -7500403 true false 218 120 240 165 255 165 278 120
Circle -7500403 true false 214 72 67
Rectangle -1 true true 164 223 179 298
Polygon -1 true true 45 285 30 285 30 240 15 195 45 210
Circle -1 true true 3 83 150
Rectangle -1 true true 65 221 80 296
Polygon -1 true true 195 285 210 285 210 240 240 210 195 210
Polygon -7500403 true false 276 85 285 105 302 99 294 83
Polygon -7500403 true false 219 85 210 105 193 99 201 83

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

wolf
false
0
Polygon -16777216 true false 253 133 245 131 245 133
Polygon -7500403 true true 2 194 13 197 30 191 38 193 38 205 20 226 20 257 27 265 38 266 40 260 31 253 31 230 60 206 68 198 75 209 66 228 65 243 82 261 84 268 100 267 103 261 77 239 79 231 100 207 98 196 119 201 143 202 160 195 166 210 172 213 173 238 167 251 160 248 154 265 169 264 178 247 186 240 198 260 200 271 217 271 219 262 207 258 195 230 192 198 210 184 227 164 242 144 259 145 284 151 277 141 293 140 299 134 297 127 273 119 270 105
Polygon -7500403 true true -1 195 14 180 36 166 40 153 53 140 82 131 134 133 159 126 188 115 227 108 236 102 238 98 268 86 269 92 281 87 269 103 269 113

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270

@#$#@#$#@
NetLogo 5.3
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
<experiments>
  <experiment name="model verification D2.3 fam 0%" repetitions="50" runMetricsEveryStep="true">
    <setup>setup</setup>
    <go>go</go>
    <metric>count turtles</metric>
    <metric>statistics_minimum_walking_speed</metric>
    <metric>statistics_maximum_walking_speed</metric>
    <metric>statistics_minimum_running_speed</metric>
    <metric>statistics_maximum_running_speed</metric>
    <metric>statistics_evacuated_door1</metric>
    <metric>statistics_evacuated_door2</metric>
    <metric>statistics_evacuated_door3</metric>
    <metric>statistics_evacuated_door4</metric>
    <metric>count turtles with [color = grey]</metric>
    <enumeratedValueSet variable="_falls">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_fire_alarm">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_staff_members">
      <value value="4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_public_announcement">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment-iccci2017-compare with first model" repetitions="60" runMetricsEveryStep="true">
    <setup>set cultural_cluster_distribution [0 0 0 0 0 0 0 0 1 0 0]
set behaviour_space_experiment_setup 1
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="false"/>
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="0"/>
      <value value="50"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="10000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report-minimum number of samples estimation" repetitions="100" runMetricsEveryStep="true">
    <setup>set cultural_cluster_distribution [0 0 0 0 0 0 0 0 1 0 0]
set behaviour_space_experiment_setup 1
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="room_environment_type">
      <value value="7"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report-default" repetitions="60" runMetricsEveryStep="true">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
set behaviour_space_experiment_setup 1
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
      <value value="6"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table1-environment1" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="false"/>
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="0"/>
      <value value="50"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table1-environment6" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="false"/>
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table2-environment1" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table2-environment6" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table3-environment1-group2" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="0"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table3-environment1-group3" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="0"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table3-environment1-group4" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="0"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table3-environment6-group2" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="0"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table3-environment6-group3" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="0"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table3-environment6-group4" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table3-environment1-alone" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="100"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table3-environment6-alone" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="100"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table4-environment1-alone50" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="0"/>
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table4-environment1-alone0-groups2" repetitions="2" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="25"/>
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="0"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table4-environment6-alone50" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="0"/>
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table4-environment6-alone0-groups2" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="0"/>
      <value value="25"/>
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
      <value value="25"/>
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="0"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table5-environment1" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="false"/>
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table5-environment6" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="false"/>
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table6-environment1" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="0"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table6-environment6" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="0"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="0"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table7-environment1" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="0"/>
      <value value="50"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table7-environment6" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
set behaviour_space_experiment_setup 1
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="0"/>
      <value value="50"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table8-environment1" repetitions="1" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="2"/>
      <value value="3"/>
      <value value="4"/>
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D2.4-032017-table8-environment6" repetitions="60" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="2"/>
      <value value="3"/>
      <value value="4"/>
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D4.2-032017-table1-environment1" repetitions="60" runMetricsEveryStep="true">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
set behaviour_space_experiment_setup 1
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="0"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="0"/>
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D4.2-032017-table1-environment6" repetitions="60" runMetricsEveryStep="true">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
set behaviour_space_experiment_setup 1
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="0"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="0"/>
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D4.2-032017-table2-environment1" repetitions="60" runMetricsEveryStep="true">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
set behaviour_space_experiment_setup 1
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="0"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
      <value value="1"/>
      <value value="2"/>
      <value value="3"/>
      <value value="4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="0"/>
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D4.2-032017-table2-environment6" repetitions="60" runMetricsEveryStep="true">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
set behaviour_space_experiment_setup 1
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="0"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
      <value value="1"/>
      <value value="2"/>
      <value value="3"/>
      <value value="4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="0"/>
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D4.2-032017-table3-environment1" repetitions="60" runMetricsEveryStep="true">
    <setup>;set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
set behaviour_space_experiment_setup 1
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
      <value value="1600"/>
      <value value="3200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="cultural_cluster_distribution">
      <value value="[0 0 0 0 0 0 0 0 1 0 0]"/>
      <value value="[0 0 0 1 0 0 0 0 0 0 0]"/>
      <value value="[0 0 0 0.5 0 0 0 0 0.5 0 0]"/>
      <value value="[0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="0"/>
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report_D4.2-032017-table3-environment6" repetitions="60" runMetricsEveryStep="true">
    <setup>;set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
set behaviour_space_experiment_setup 1
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="number_passengers">
      <value value="1600"/>
      <value value="3200"/>
      <value value="6400"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="cultural_cluster_distribution">
      <value value="[0 0 0 0 0 0 0 0 1 0 0]"/>
      <value value="[0 0 0 1 0 0 0 0 0 0 0]"/>
      <value value="[0 0 0 0.5 0 0 0 0 0.5 0 0]"/>
      <value value="[0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="0"/>
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="room_environment_type">
      <value value="6"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="report-default" repetitions="4" runMetricsEveryStep="false">
    <setup>set cultural_cluster_distribution [0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09 0.09]
set behaviour_space_experiment_setup 1
setup</setup>
    <go>go</go>
    <metric>ticks</metric>
    <metric>statistics_average_resp_time_from_decide_evacuate</metric>
    <metric>statistics_evacuation_time</metric>
    <metric>statistics_falls_total</metric>
    <metric>statistics_falls_average_per_passenger</metric>
    <metric>statistics_average_resp_time_from_start_fire</metric>
    <metric>statistics_average_resp_time_from_observation_fire</metric>
    <metric>statistics_average_resp_time_from_fire_alarm</metric>
    <metric>statistics_average_desire_evacuate</metric>
    <metric>statistics_average_fear</metric>
    <metric>statistics_average_belief_dangerous</metric>
    <metric>statistics_average_desire_walkrand</metric>
    <metric>statistics_average_intention_walkrand</metric>
    <metric>statistics_average_intention_evacuate</metric>
    <enumeratedValueSet variable="number_passengers">
      <value value="800"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_contagion_model">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_familiarity">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_help">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_falls">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exit_lighting">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_number_staff_members">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ACTION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_FIRE_ALARM_ACTION">
      <value value="181"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="START_PA_ACTION">
      <value value="201"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="PLACE_FIRE_POSITION">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_children">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_eldery">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_2_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_3_ratio">
      <value value="33"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_groups_of_4_ratio">
      <value value="34"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_females">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_percentage_people_traveling_alone">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="room_environment_type">
      <value value="1"/>
    </enumeratedValueSet>
  </experiment>
</experiments>
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180

@#$#@#$#@
0
@#$#@#$#@
