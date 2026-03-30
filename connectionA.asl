/* =============================================================================
   GLOBAL SETUP, STATE & HELPERS
   ============================================================================= */

/* ------------------------------
   State
   ------------------------------ */
nav_mode(explore).          /* explore | goto */
nav_target(0,0).            /* relative target */
explore_dir(e).             /* e | s | w | n */
turn_counter(0).            /* periodic turns */
stuck_count(0).             /* consecutive failures */
avoid_dir(none).            /* one-step avoid direction */
sidestep_streak(0).         /* steps to stay in sidestep dir - Added by Member 4 */
sidestep_dir(none).         /* sticky sidestep direction - Added by Member 4 */
/* Optimized stickiness: 3 ensures we clear most clumps - Added by Member 4 */
sidestep_duration(3).
waiting_for_block(false).   /* waiting after request */
at_dispenser(none).         /* direction of dispenser when waiting */
rotation_attempts(0).       /* submit retry counter (0-4); reset on fresh goal visit */
spin_cycles(0).             /* full 4-rotation cycles completed (0-2) - Added by Member 4 */
nudge_cooldown(0).          /* steps to explore after a nudge (prevents re-clumping) - Added by Member 4 */
last_pos(0,0).              /* for stuck detection - Added by Member 4 */
last_dist(9999).            /* for oscillation detection - Added by Member 4 */
progress_stuck(0).          /* steps without getting closer to target - Added by Member 4 */
rotation_dir(cw).            /* Dynamic choice of rotation - Added by Member 4 */
last_fail_dir(none).        /* Prevent oscillating loops - Added by Member 4 */
last_fail_count(0).         /* Steps remaining for direction penalty - Added by Member 4 */
blacklisted_goal(0, 0, 0).  /* RX, RY, StepsRemaining - Added by Member 4 */

/* Startup */
!start.
+!start : true <- true.


/* =============================================================================
   Always-act entry point
   ============================================================================= */
+actionID(_) : true <- // Modified by Member 4
    !coordinate;
    !update_recovery;
    !update_cooldowns;
    !update_carrying_beliefs;
    !cleanup_stale_memory;
    !decide_action.

// Maintenance for attachment beliefs to prevent percept flickering - Added by Member 4
+!update_carrying_beliefs : lastAction(attach) & lastActionResult(success) & my_task(T, Reqs) & next_needed_type(Reqs, Type) <-
    ?lastActionParams([Dir]);
    +carrying(Dir, Type);
    .print(">>> BRAIN: Recorded attachment of ", Type, " at ", Dir).

+!update_carrying_beliefs : lastAction(rotate) & lastActionResult(success) & carrying(Dir, Type) <-
    ?lastActionParams([Mode]);
    !rotate_dir_belief(Dir, Mode, NewDir);
    -carrying(Dir, Type); +carrying(NewDir, Type).

+!update_carrying_beliefs : lastAction(detach) & lastActionResult(success) <-
    ?lastActionParams([Dir]); -carrying(Dir, _).

+!update_carrying_beliefs : lastAction(submit) & lastActionResult(success) <-
    .findall(D, carrying(D, T), L); !clear_carrying(L).

// Sync carrying beliefs with world percepts for total integrity - Added by Member 4
+!update_carrying_beliefs : not attached(_, _) & carrying(Dir, Type) <- 
    -carrying(Dir, Type).
+!update_carrying_beliefs : attached(AX, AY) & adjacent_dir(AX, AY, Dir) & thing(AX, AY, block, Type) & not carrying(Dir, Type) <- 
    +carrying(Dir, Type).

+!update_carrying_beliefs : true.

+!rotate_dir_belief(n, cw, e). +!rotate_dir_belief(e, cw, s). +!rotate_dir_belief(s, cw, w). +!rotate_dir_belief(w, cw, n). // Added by Member 4
+!rotate_dir_belief(n, ccw, w). +!rotate_dir_belief(w, ccw, s). +!rotate_dir_belief(s, ccw, e). +!rotate_dir_belief(e, ccw, n). // Added by Member 4

+!clear_carrying([]) : true. // Added by Member 4
+!clear_carrying([D|Rest]) : true <- -carrying(D, _); !clear_carrying(Rest). // Added by Member 4

+!update_cooldowns : nudge_cooldown(C) & C > 0 <- 
    -nudge_cooldown(C); +nudge_cooldown(C-1). // Added by Member 4
+!update_cooldowns : last_fail_count(C) & C > 0 <-
    -last_fail_count(C); +last_fail_count(C-1).
+!update_cooldowns : blacklisted_goal(X, Y, C) & C > 0 <-
    -blacklisted_goal(X, Y, C); +blacklisted_goal(X, Y, C-1). 
+!update_cooldowns : true. // Added by Member 4

+!cleanup_stale_memory : found_goal(0,0) & not goal(0,0) & not thing(0,0,goal,_) <- // Added by Member 4
    -found_goal(0,0); 
    .print(">>> BRAIN: Cleared stale goal memory at (0,0)").
+!cleanup_stale_memory : found_dispenser(T,0,0) & not thing(0,0,dispenser,T) <- // Added by Member 4
    -found_dispenser(T,0,0); .print(">>> BRAIN: Cleared stale dispenser memory at (0,0)").
+!cleanup_stale_memory : true. // Added by Member 4

/* =============================================================================
   API for teammates
   ============================================================================= */
// Belief-event handlers (triggered when teammate sends a tell message)
+set_target(Tx,Ty) : true <-
    -nav_target(_,_); +nav_target(Tx,Ty);
    -nav_mode(_); +nav_mode(goto).

+clear_target : true <-
    -nav_mode(_); +nav_mode(explore);
    -nav_target(_,_); +nav_target(0,0).

// BUG FIX 5: Record dispensers and goals into memory when first seen via percepts.
// To prevent memory bloat (causing lag after 100 steps), we only record "new"
// locations that are at least 7 tiles away from any already-known location.
+thing(X, Y, dispenser, Type)
    : not (found_dispenser(Type, X2, Y2) & math.abs(X-X2) + math.abs(Y-Y2) < 7) <-
    +found_dispenser(Type, X, Y).

+goal(X, Y)
    : not (found_goal(X2, Y2) & math.abs(X-X2) + math.abs(Y-Y2) < 7) <-
    +found_goal(X, Y).
is_adjacent(X, Y, Dir) :-
    adjacent_dir(X, Y, Dir).

adjacent_dir(0, 1, s).
adjacent_dir(0,-1, n).
adjacent_dir(1, 0, e).
adjacent_dir(-1,0, w).

is_on_target(0, 0).
/* =============================================================================
   Helper predicates
   ============================================================================= */

/* Collisions:
   Include entities (other agents) as blocked to avoid repeated failed path attempts.
   IMPORTANT: exclude own attached blocks - agent can carry them while moving. */
cell_blocked(X,Y) :- obstacle(X,Y).
cell_blocked(X,Y) :- thing(X,Y,block,_) & not attached(X,Y).
cell_blocked(X,Y) :- thing(X,Y,dispenser,_).
cell_blocked(X,Y) :- thing(X,Y,entity,_) & (X \== 0 | Y \== 0).  // Blocked by other agents

/* Avoid last failed direction and penalized directions (cooldown) */
dir_clear(D) :- 
    not cell_blocked_dir(D) & 
    (not (avoid_dir(A) & A == D)) &
    (not (last_fail_dir(D) & last_fail_count(C) & C > 0)).

cell_blocked_dir(e) :- cell_blocked(1,0).
cell_blocked_dir(w) :- cell_blocked(-1,0).
cell_blocked_dir(n) :- cell_blocked(0,-1).
cell_blocked_dir(s) :- cell_blocked(0,1).

/* Abs - Added by Member 4 */
abs(X,AX) :- X >= 0 & AX = X.
abs(X,AX) :- X <  0 & AX = -X.

/* Choose primary direction by larger axis magnitude - Modified by Member 4 */
choose_primary(Tx,Ty,e) :- abs(Tx,AX) & abs(Ty,AY) & AX >= AY & Tx > 0.
choose_primary(Tx,Ty,w) :- abs(Tx,AX) & abs(Ty,AY) & AX >= AY & Tx < 0.
choose_primary(Tx,Ty,s) :- abs(Tx,AX) & abs(Ty,AY) & AY >  AX & Ty > 0.
choose_primary(Tx,Ty,n) :- abs(Tx,AX) & abs(Ty,AY) & AY >  AX & Ty < 0.

/* Update target after move - Modified by Member 4 */
new_target(e,Tx,Ty,NTx,Ty) :- NTx = Tx - 1.
new_target(w,Tx,Ty,NTx,Ty) :- NTx = Tx + 1.
new_target(s,Tx,Ty,Tx,NTy) :- NTy = Ty - 1.
new_target(n,Tx,Ty,Tx,NTy) :- NTy = Ty + 1.
/* Update memory of all relative coordinates after move - Rewritten by Member 4 */
+!update_coordinate_memory(Dir) : true <-
    .findall(found_goal(X,Y), found_goal(X,Y), GL);
    !update_goals(Dir, GL);
    .findall(found_dispenser(T,X,Y), found_dispenser(T,X,Y), DL);
    !update_dispensers(Dir, DL).

+!update_goals(_, []) : true.
+!update_goals(Dir, [found_goal(X,Y)|Rest]) : true <-
    -found_goal(X,Y);
    ?new_target(Dir,X,Y,NX,NY);
    +found_goal(NX,NY);
    !update_goals(Dir, Rest).

+!update_dispensers(_, []) : true.
+!update_dispensers(Dir, [found_dispenser(T,X,Y)|Rest]) : true <-
    -found_dispenser(T,X,Y);
    ?new_target(Dir,X,Y,NX,NY);
    +found_dispenser(T,NX,NY);
    !update_dispensers(Dir, Rest).
/* =============================================================================
   MEMBER 1: Navigation & Exploration (Parser-safe, Low-noise)
   -----------------------------------------------------------------------------
   Features:
   - Always-act (every actionID -> exactly one action)
   - Greedy moveToward target (axis by larger |dx| or |dy|)
   - Sidestep when blocked
   - Recovery on failed_path / failed_forbidden (avoid last direction)
   - Systematic exploration (stateful heading + periodic rotation)
   - Print before each move/skip: direction and reason (optional; remove for low-noise)

   Assumed percept beliefs:
   - obstacle(X,Y)
   - thing(X,Y,Type,Details) with Type: block | dispenser | entity | marker | ...
   - lastActionResult(Result)
   - lastAction(Action)
   - lastActionParams([Dir])
   ============================================================================= */
/* =============================================================================
   Recovery update
   ============================================================================= */
+!check_if_stuck : stuck_count(C) & C >= 2 <-
    +i_am_stuck.
+!check_if_stuck : true.

/* Successful move: update target (if goto and not already 0,0) and bump turn counter; clear avoid_dir, dec_stuck */
+!update_recovery : lastActionResult(success) & lastAction(move) & lastActionParams([Dir]) & nav_mode(goto) & nav_target(Tx,Ty) & Tx > 0 <-
    -sent_move_last_step(_);
    ?new_target(Dir,Tx,Ty,NTx,NTy);
    -nav_target(Tx,Ty); +nav_target(NTx,NTy);
    -avoid_dir(_); +avoid_dir(none);
    !dec_stuck;
    !update_coordinate_memory(Dir);
    !bump_turn_counter.
/* Universal Progress Update for any successful move - Added by Member 4 */
+!update_progress_on_move : nav_target(TX, TY) & last_dist(LD) & (math.abs(TX) + math.abs(TY)) < LD <-
    -progress_stuck(_); +progress_stuck(0);
    -last_dist(_); +last_dist(math.abs(TX) + math.abs(TY));
    !check_progress_stuck.
+!update_progress_on_move : nav_target(TX, TY) <-
    ?progress_stuck(PS);
    -progress_stuck(_); +progress_stuck(PS + 1);
    -last_dist(_); +last_dist(math.abs(TX) + math.abs(TY));
    !check_progress_stuck.
+!update_progress_on_move : true.

+!check_progress_stuck : progress_stuck(PS) & PS >= 8 <-
    .print(">>> BRAIN: No progress toward target for 8 steps. Forcing escape step.");
    -progress_stuck(_); +progress_stuck(0);
    !escape_step.
+!check_progress_stuck : true.

+!update_recovery : lastActionResult(success) & lastAction(move) & lastActionParams([Dir]) & nav_mode(goto) & nav_target(Tx,Ty) <-
    -sent_move_last_step(_);
    ?new_target(Dir,Tx,Ty,NTx,NTy);
    -nav_target(Tx,Ty); +nav_target(NTx,NTy);
    -avoid_dir(_); +avoid_dir(none);
    -stuck_count(_); +stuck_count(0);
    !update_coordinate_memory(Dir);
    !update_progress_on_move;
    !bump_turn_counter.

+!update_recovery : lastActionResult(success) & lastAction(move) & lastActionParams([Dir]) <-
    -sent_move_last_step(_);
    -avoid_dir(_); +avoid_dir(none);
    -stuck_count(_); +stuck_count(0);
    !update_coordinate_memory(Dir);
    !update_progress_on_move;
    !bump_turn_counter.

/* Handle failures */
+!update_recovery : not lastActionResult(success) & lastAction(move) & lastActionParams([Dir]) <-
    -sent_move_last_step(_);
    !inc_stuck;
    ?stuck_count(SC);
    -avoid_dir(_); +avoid_dir(Dir);
    -last_fail_dir(_); +last_fail_dir(Dir);
    -last_fail_count(_); +last_fail_count(4);
    // If we were moving to a specific 1-step target, penalize that tile specifically
    if (nav_target(TX, TY) & (math.abs(TX) + math.abs(TY)) == 1) {
       -blacklisted_goal(TX, TY, _); +blacklisted_goal(TX, TY, 50);
       .print(">>> BRAIN: Tile (", TX, ",", TY, ") blocked! Blacklisting goal tile for 50 steps.");
    }
    .print(">>> BRAIN: Move (", Dir, ") failed (", lastActionResult, "). Penalizing direction for 4 steps. Stuck count: ", SC);
    !check_if_stuck.

+!update_recovery : not lastActionResult(success) & lastAction(rotate) & rotation_dir(Dir) <-
    -sent_move_last_step(_);
    !inc_stuck;
    ?stuck_count(SC);
    /* Toggle direction on failure to handle map edges or obstacles */
    if (Dir == cw) { -rotation_dir(_); +rotation_dir(ccw); } else { -rotation_dir(_); +rotation_dir(cw); }
    .print(">>> BRAIN: Rotate (", Dir, ") failed (", lastActionResult, "). Switching preference. Stuck count: ", SC);
    !check_if_stuck.

+!update_recovery : not lastActionResult(success) & (lastAction(attach) | lastAction(request)) & attached(_,_) <-
    -sent_move_last_step(_);
    .print(">>> BRAIN: Attach/Request failed but block already attached. Ignoring failure.").

+!update_recovery : not lastActionResult(success) & (lastAction(attach) | lastAction(request)) <-
    -sent_move_last_step(_);
    !inc_stuck;
    ?stuck_count(SC);
    .print(">>> BRAIN: Action (", lastAction, ") failed (", lastActionResult, "). Stuck count: ", SC);
    !check_if_stuck.

+!update_recovery : not lastActionResult(success) <-
    -sent_move_last_step(_);
    !inc_stuck;
    ?stuck_count(SC);
    .print(">>> BRAIN: Action (", lastAction, ") failed (", lastActionResult, "). Stuck count: ", SC);
    !check_if_stuck.

/* We sent a move last step but server skipped feedback: clear flag but do NOT update target/turn. */
+!update_recovery : sent_move_last_step(Dir) <-
    -sent_move_last_step(Dir);
    -avoid_dir(_); +avoid_dir(none);
    !dec_stuck;
    !update_coordinate_memory(Dir);
    !update_my_pos(Dir).

+!update_recovery : true <-
    -avoid_dir(_); +avoid_dir(none);
    !dec_stuck.



/* Set "sent move" flag then move (so next step we skip target update if env didn't send failure) - Modified by Member 4 */
+!do_move(Dir) : true <-
    -sidestep_streak(S); +sidestep_streak(math.max(0, S-1)); 
    -sent_move_last_step(_); +sent_move_last_step(Dir);
    move(Dir).

/* =============================================================================
   moveToward: greedy + sidestep + escape when stuck
   ============================================================================= */

/* Already on target */
+!moveToward(0,0) : true <- skip.

/* If stuck >=2, do escape step */
+!moveToward(_,_) : stuck_count(C) & C >= 2 <-
    !escape_step.

/* sticky sidestep: if we are in a streak, keep going - Added by Member 4 */
+!moveToward(Tx,Ty) : sidestep_streak(S) & S > 0 & sidestep_dir(D) & dir_clear(D) <-
    ?sidestep_duration(Dur);
    .print("move ", D, " (reason: sticky sidestep ", S, "/", Dur, ")");
    !do_move(D).

+!set_sidestep(Dir) : sidestep_duration(Dur) <- // Added by Member 4
    -sidestep_dir(_); +sidestep_dir(Dir);
    -sidestep_streak(_); +sidestep_streak(Dur).

/* Basic greedy case - Added by Member 4: set nav_target for blacklisting */
+!moveToward(Tx,Ty) : true <-
    -nav_target(_,_); +nav_target(Tx,Ty);
    !greedy_step(Tx,Ty).

/* Greedy: choose primary direction by magnitude */
+!greedy_step(Tx,Ty) : choose_primary(Tx,Ty,Dir) & dir_clear(Dir) <-
    -sidestep_streak(_); +sidestep_streak(0); // Clear streak on successful primary move
    .print("move ", Dir, " (reason: greedy toward target)");
    !do_move(Dir).

/* Primary blocked -> sidestep */
+!greedy_step(Tx,Ty) : choose_primary(Tx,Ty,Dir) & not dir_clear(Dir) <-
    !sidestep(Dir,Tx,Ty).

/* No direction chosen -> explore */
+!greedy_step(_,_) : true <-
    -sidestep_streak(_); +sidestep_streak(0);
    !explore.

/* Sidestep rules: NEVER move in opposite direction (causes oscillation + target drift).
   Always use perpendicular directions only. */

/* Primary east blocked: prefer s/n based on Ty, with 10% random flip to break oscillations - Modified by Member 4 */
+!sidestep(e,_,Ty) : Ty > 0 & .random(R) & R < 0.1 & dir_clear(n) <- !set_sidestep(n); !do_move(n).
+!sidestep(e,_,Ty) : Ty > 0 & dir_clear(s)                   <- !set_sidestep(s); !do_move(s).

+!sidestep(e,_,Ty) : Ty < 0 & .random(R) & R < 0.1 & dir_clear(s) <- !set_sidestep(s); !do_move(s).
+!sidestep(e,_,Ty) : Ty < 0 & dir_clear(n)                   <- !set_sidestep(n); !do_move(n).

+!sidestep(e,_,_) : dir_clear(s) <- !set_sidestep(s); !do_move(s).
+!sidestep(e,_,_) : dir_clear(n) <- !set_sidestep(n); !do_move(n).

/* Primary west blocked: prefer s/n based on Ty, with 10% random flip */
+!sidestep(w,_,Ty) : Ty > 0 & .random(R) & R < 0.1 & dir_clear(n) <- !set_sidestep(n); !do_move(n).
+!sidestep(w,_,Ty) : Ty > 0 & dir_clear(s)                   <- !set_sidestep(s); !do_move(s).

+!sidestep(w,_,Ty) : Ty < 0 & .random(R) & R < 0.1 & dir_clear(s) <- !set_sidestep(s); !do_move(s).
+!sidestep(w,_,Ty) : Ty < 0 & dir_clear(n)                   <- !set_sidestep(n); !do_move(n).

+!sidestep(w,_,_) : dir_clear(s) <- !set_sidestep(s); !do_move(s).
+!sidestep(w,_,_) : dir_clear(n) <- !set_sidestep(n); !do_move(n).

/* Primary north blocked: prefer e/w based on Tx, with 10% random flip - Modified by Member 4 */
+!sidestep(n,Tx,_) : Tx > 0 & .random(R) & R < 0.1 & dir_clear(w) <- !set_sidestep(w); !do_move(w).
+!sidestep(n,Tx,_) : Tx > 0 & dir_clear(e)                   <- !set_sidestep(e); !do_move(e).

+!sidestep(n,Tx,_) : Tx < 0 & .random(R) & R < 0.1 & dir_clear(e) <- !set_sidestep(e); !do_move(e).
+!sidestep(n,Tx,_) : Tx < 0 & dir_clear(w)                   <- !set_sidestep(w); !do_move(w).

+!sidestep(n,_,_) : dir_clear(e) <- !set_sidestep(e); !do_move(e).
+!sidestep(n,_,_) : dir_clear(w) <- !set_sidestep(w); !do_move(w).

/* Primary south blocked: prefer e/w based on Tx, with 10% random flip - Modified by Member 4 */
+!sidestep(s,Tx,_) : Tx > 0 & .random(R) & R < 0.1 & dir_clear(w) <- !set_sidestep(w); !do_move(w).
+!sidestep(s,Tx,_) : Tx > 0 & dir_clear(e)                   <- !set_sidestep(e); !do_move(e).

+!sidestep(s,Tx,_) : Tx < 0 & .random(R) & R < 0.1 & dir_clear(e) <- !set_sidestep(e); !do_move(e).
+!sidestep(s,Tx,_) : Tx < 0 & dir_clear(w)                   <- !set_sidestep(w); !do_move(w).

+!sidestep(s,_,_) : dir_clear(e) <- !set_sidestep(e); !do_move(e).
+!sidestep(s,_,_) : dir_clear(w) <- !set_sidestep(w); !do_move(w).

+!sidestep(_,_,_) : true <-
    !escape_step.

/* Escape step when stuck: perform a random jump move to break clumps - Added by Member 4 */
+!escape_step : dir_clear(D) <- 
    .print("(reason: escape step - jumping tile to clear space)");
    !do_move(D).
+!escape_step : true <-
    .print("(reason: escape step - rotating heading)");
    !rotate_explore_dir;
    !explore_step.

/* Target and turn_counter are updated in !update_recovery when lastActionResult(success) (next step). */

/* =============================================================================
   Systematic exploration
   ============================================================================= */

/* Systematic exploration: move in explore_dir; rotate if blocked or periodically */
+!explore : true <-
    !explore_step.

/* Try current heading; if blocked rotate and try again; else try any; else skip */
+!explore_step : explore_dir(D) & dir_clear(D) <-
    .print("move ", D, " (reason: explore heading)");
    !do_move(D).

+!explore_step : explore_dir(D) & not dir_clear(D) <-
    !rotate_explore_dir;
    !explore_step2.

// If stuck for a while in explore, force a target to an old memory to "jump" regions
+!explore_step : stuck_count(SC) & SC >= 5 <-
    .print(">>> BRAIN: Exploring same area too long. Heading toward landmark memory.");
    !head_toward_any_memory.

+!explore_step : true <-
    !try_any_dir_or_skip.

+!head_toward_any_memory : found_dispenser(_, X, Y) <- !moveToward(X, Y).
+!head_toward_any_memory : found_goal(X, Y) <- !moveToward(X, Y).
+!head_toward_any_memory : true <- !rotate_explore_dir; !rotate_explore_dir; !explore_step2.

/* After one rotation */
+!explore_step2 : explore_dir(D) & dir_clear(D) <-
    .print("move ", D, " (reason: explore after rotate)");
    !do_move(D).

+!explore_step2 : true <-
    !try_any_dir_or_skip.

/* Try any direction based on heading (NO inline if) */

/* heading e: try s, w, n */
+!try_any_dir_or_skip : explore_dir(e) & dir_clear(s) <-
    .print("move ", s, " (reason: explore try any, heading blocked)");
    !do_move(s).
+!try_any_dir_or_skip : explore_dir(e) & dir_clear(w) <-
    .print("move ", w, " (reason: explore try any, heading blocked)");
    !do_move(w).
+!try_any_dir_or_skip : explore_dir(e) & dir_clear(n) <-
    .print("move ", n, " (reason: explore try any, heading blocked)");
    !do_move(n).

/* heading s: try w, n, e */
+!try_any_dir_or_skip : explore_dir(s) & dir_clear(w) <-
    .print("move ", w, " (reason: explore try any, heading blocked)");
    !do_move(w).
+!try_any_dir_or_skip : explore_dir(s) & dir_clear(n) <-
    .print("move ", n, " (reason: explore try any, heading blocked)");
    !do_move(n).
+!try_any_dir_or_skip : explore_dir(s) & dir_clear(e) <-
    .print("move ", e, " (reason: explore try any, heading blocked)");
    !do_move(e).

/* heading w: try n, e, s */
+!try_any_dir_or_skip : explore_dir(w) & dir_clear(n) <-
    .print("move ", n, " (reason: explore try any, heading blocked)");
    !do_move(n).
+!try_any_dir_or_skip : explore_dir(w) & dir_clear(e) <-
    .print("move ", e, " (reason: explore try any, heading blocked)");
    !do_move(e).
+!try_any_dir_or_skip : explore_dir(w) & dir_clear(s) <-
    .print("move ", s, " (reason: explore try any, heading blocked)");
    !do_move(s).

/* heading n: try e, s, w */
+!try_any_dir_or_skip : explore_dir(n) & dir_clear(e) <-
    .print("move ", e, " (reason: explore try any, heading blocked)");
    !do_move(e).
+!try_any_dir_or_skip : explore_dir(n) & dir_clear(s) <-
    .print("move ", s, " (reason: explore try any, heading blocked)");
    !do_move(s).
+!try_any_dir_or_skip : explore_dir(n) & dir_clear(w) <-
    .print("move ", w, " (reason: explore try any, heading blocked)");
    !do_move(w).

/* None possible based on safety checks? TRY ANYWAY. The teammate might move! */
+!try_any_dir_or_skip : true <-
    .print(">>> BRAIN: All dirs seemingly blocked. Attempting panic move to break deadlock.");
    -avoid_dir(_); +avoid_dir(none);
    .random(R);
    !panic_move(R).

+!panic_move(R) : R < 0.25 <- move(n).
+!panic_move(R) : R < 0.5  <- move(s).
+!panic_move(R) : R < 0.75 <- move(e).
+!panic_move(R) : true     <- move(w).

/* Rotate explore heading clockwise */
+!rotate_explore_dir : explore_dir(e) <- -explore_dir(e); +explore_dir(s).
+!rotate_explore_dir : explore_dir(s) <- -explore_dir(s); +explore_dir(w).
+!rotate_explore_dir : explore_dir(w) <- -explore_dir(w); +explore_dir(n).
+!rotate_explore_dir : explore_dir(n) <- -explore_dir(n); +explore_dir(e).
+!rotate_explore_dir : true          <- -explore_dir(_); +explore_dir(e).

/* Rotate every 12 moves */
+!bump_turn_counter : turn_counter(K) & K == 11 <-
    -turn_counter(K); +turn_counter(0);
    !rotate_explore_dir.

+!bump_turn_counter : turn_counter(K) <-
    NK = K + 1;
    -turn_counter(K); +turn_counter(NK).

+!bump_turn_counter : true <-
    +turn_counter(1).

/* =============================================================================
   Stuck counter helpers
   ============================================================================= */
+!inc_stuck : stuck_count(0) <- -stuck_count(0); +stuck_count(1).
+!inc_stuck : stuck_count(1) <- -stuck_count(1); +stuck_count(2).
+!inc_stuck : stuck_count(2) <- true.
+!inc_stuck : true          <- -stuck_count(_); +stuck_count(1).

+!dec_stuck : stuck_count(2) <- -stuck_count(2); +stuck_count(1).
+!dec_stuck : stuck_count(1) <- -stuck_count(1); +stuck_count(0).
+!dec_stuck : true          <- -stuck_count(_); +stuck_count(0).

/* =============================================================================
   MEMBER 2: Coordinator & Task Manager (Brain)
   -----------------------------------------------------------------------------
   Features:
   - Centralized coordination (connectionA1 is leader)
   - Task selection logic (1-block priority, then 2-block)
   - Belief management: assigned(task, agent), task_status(task, status), need(type, qty)
   - Handling failures: Reassigns if agent is stuck or task disappears
   ============================================================================= */

/* Rules for Member 2 */
is_leader :- .my_name(connectionA1).

// Task categorization rules
is_one_block(T) :- task(T, _, _, Reqs) & .length(Reqs, 1).
is_two_block(T) :- task(T, _, _, Reqs) & .length(Reqs, 2).
// solvable_req: a requirement whose position is a CARDINAL adjacent cell.
// Only these are achievable by a single agent (attach from that direction + rotation).
// Diagonal positions like (-1,1) are distance √2 — unreachable via rotation.
solvable_req(req(0, 1, T), T).   // south
solvable_req(req(0,-1, T), T).   // north
solvable_req(req(1, 0, T), T).   // east
solvable_req(req(-1,0, T), T).   // west

// Find the first solvable (cardinal-position) req in a list
first_solvable([Req|_], Req) :- solvable_req(Req, _).
first_solvable([_|Rest], Req) :- first_solvable(Rest, Req).

// Helper: Find a free agent (leader or follower)
free_agent(Ag) :- 
    .member(Ag, [connectionA1, connectionA2, connectionA3, connectionA4, connectionA5]) & 
    not assigned(_, Ag).
/* ------------------------------
   Coordination Plans (Leader only)
   ------------------------------ */

+!coordinate : is_leader <-
    !cleanup_stale_tasks;
    !assign_all_tasks.
+!coordinate : true.

// Remove assignments for tasks that no longer exist in the environment
+!cleanup_stale_tasks : true <- // Modified by Member 4
    // FIX: Sticky assignments. Do NOT cancel a task if the agent is already in 
    // the 'submitting' phase (actually at the goal), unless the task is totally gone.
    .findall(T, (assigned(T, Ag) & not task(T,_,_,_) & not task_status(T, submitting)), StaleList);
    !do_cleanup(StaleList).

+!do_cleanup([]) : true.
+!do_cleanup([T|Rest]) : assigned(T, Ag) <- // Modified by Member 4
    -assigned(T, Ag);
    -task_status(T, _);
    !cleanup_need(T);
    .send(Ag, tell, task_cancelled(T));
    !do_cleanup(Rest).
+!do_cleanup([_|Rest]) : true <- // Added by Member 4
    !do_cleanup(Rest).

// Task Assignment prioritization:
// Priority 1: 1-block tasks (directly assignable, always solvable).
// Priority 2: 2-block tasks — extract the first SOLVABLE (cardinal-position) requirement
//             and send it as a 1-block sub-task. Diagonal reqs like req(-1,1,b1)
//             can NEVER be satisfied by a single agent via attach+rotation, so they
//             are skipped. The agent receives [SolvableReq] as a 1-element list.
+!assign_all_tasks : true <-
    !assign_priority_1.
    //!assign_priority_2.

+!assign_priority_1 : task(T,_,_,[Req]) & solvable_req(Req, _) & not assigned(T,_) & not task_blocked(T) & free_agent(Ag) <- // Modified by Member 4
    +assigned(T, Ag);
    +task_status(T, collecting);
    .send(Ag, achieve, start_task(T, [Req]));
    !assign_priority_1.
+!assign_priority_1 : true.

+!assign_priority_2 : true. // Modified by Member 4

+!assign_priority_2 : true. // We will write our new logic here!


/* ------------------------------
   Agent Status/Task Plans (All Agents)
   ------------------------------ */

+!start_task(T, Reqs) : true <- // Modified by Member 4
    -my_task(_, _); // Ensure we don't have multiple active task beliefs
    -waiting_for_block(_); +waiting_for_block(false);
    +my_task(T, Reqs);
    .print(">>> BRAIN: Assigned to task: ", T).


// MODIFIED BY MEMBER 4 (Ghalya): Clean up my_role, my_partner, and blueprint upon cancellation
+task_cancelled(T) : my_task(T, _) <- // Modified by Member 4
    -my_task(T, _);
    .print(">>> BRAIN: Task ", T, " was cancelled.");
    -waiting_for_block(_); +waiting_for_block(false);
    -at_dispenser(_); +at_dispenser(none);
    -wait_steps(_); +wait_steps(0);
    -rotation_attempts(_); +rotation_attempts(0);
    -spin_cycles(_); +spin_cycles(0);
    !clear_target.

// Failure handling: if I'm stuck, tell the leader to reassign my task
+i_am_stuck : my_task(T, _) <- // Modified by Member 4
    .send(connectionA1, tell, agent_stuck_on(T));
    -my_task(T, _);
    -waiting_for_block(_); +waiting_for_block(false);
    -at_dispenser(_); +at_dispenser(none);
    !clear_target.
+i_am_stuck : true.



// BUG FIX 1: !clear_target was called as a plan but only existed as a belief handler.
// Added the matching plan so !clear_target invocations don't silently fail.
+!clear_target : true <-
    -nav_mode(_); +nav_mode(explore);
    -nav_target(_,_); +nav_target(0,0).

// BUG FIX 2: !set_target mirrored fix — plan version for direct invocation.
+!set_target(Tx,Ty) : true <-
    -nav_target(_,_); +nav_target(Tx,Ty);
    -nav_mode(_); +nav_mode(goto).

// Leader handles completion reports
+task_completed(T)[source(Ag)] : is_leader <-
    .print(">>> BRAIN: Agent ", Ag, " completed task ", T);
    -assigned(T, Ag);
    -task_status(T, _);
    !cleanup_need(T);
    !coordinate.

// Leader handles stuck agent report - reassign that task
+agent_stuck_on(T)[source(Ag)] : is_leader <- // Modified by Member 4
    .print(">>> BRAIN: Agent ", Ag, " stuck on task ", T, ". Reassigning.");
    -assigned(T, Ag);
    // FIX: Add a cooldown so we don't re-assign the SAME task to the SAME agent immediately.
    +stuck_cooldown(Ag, T, 20);
    -task_status(T, _);
    !cleanup_need(T);
    !coordinate.
+agent_stuck_on(_)[source(_)] : true.


// -----------------------------------------------------------------------
// Task Error Handling
// -----------------------------------------------------------------------

// Agent self-abandoned an unsolvable task - Added by Member 4
+task_failed(T)[source(Ag)] : is_leader <-
    .print(">>> BRAIN: Agent ", Ag, " ABANDONED unsolvable task ", T, ". Blocking it.");
    +task_blocked(T);    // mark as blocked so assign_priority_1 skips it
    -assigned(T, _);
    -task_status(T, _);
    !coordinate.
+task_failed(_)[source(_)] : true.

// Remove the need() belief for a completed/cancelled task
+!cleanup_need(T) : task(T, _, _, [req(_,_,Type)|_]) <-
    -need(Type, _).
+!cleanup_need(_) : true.

/* =============================================================================
   MEMBER 3: Collector Logic
   -----------------------------------------------------------------------------
   Features:
   - Identify nearest dispensers and goals from percepts
   - Attachment tracking (carrying_block)
   - State machine: move to dispenser -> request -> attach -> move to goal -> submit
   - Automatic target updating for Navigation (Member 1)
   ============================================================================= */

/* Helper Predicates to find things in vision and memory */
find_dispenser(Type, X, Y) :- thing(X, Y, dispenser, Type).
find_dispenser(Type, X, Y) :- found_dispenser(Type, X, Y).

find_goal(X, Y) :- goal(X, Y).
find_goal(X, Y) :- thing(X, Y, goal, _).
find_goal(X, Y) :- found_goal(X, Y).

// Helper: Find the NEAREST dispenser/goal among all known (percepts + memory)
find_nearest_dispenser(Type, NX, NY) :- 
    .findall([math.abs(X)+math.abs(Y), X, Y], find_dispenser(Type, X, Y), L) & 
    L \== [] & .sort(L, [[_, NX, NY]|_]).

find_best_goal(X, Y) :- // Priority 1: Clear, uncrowded, non-blacklisted, block-safe goal
    .findall([Dist, GX, GY], (
        find_goal(GX, GY) & 
        Dist = math.abs(GX) + math.abs(GY) & 
        not cell_blocked(GX, GY) &      // Not a wall/dispenser
        not blacklisted_goal(GX, GY, _) & // Not recently failed
        not teammate_at(GX, GY) &         // Not occupied
        not attached_block_blocked(GX, GY) // Block won't hit a wall
    ), Goals) &
    .sort(Goals, SortedGoals) &
    SortedGoals = [[_, X, Y]|_].

// Helper: If I move to (GX, GY), will my block (AX, AY) hit an obstacle?
attached_block_blocked(GX, GY) :-
    attached(AX, AY) & cell_blocked(GX + AX, GY + AY).

find_best_goal(X, Y) :- // Priority 2: Any clear goal (ignoring teammates)
    .findall([Dist, GX, GY], (
        find_goal(GX, GY) & 
        Dist = math.abs(GX) + math.abs(GY) & 
        not cell_blocked(GX, GY)
    ), Goals) &
    .sort(Goals, SortedGoals) &
    SortedGoals = [[_, X, Y]|_].

find_best_goal(X, Y) :- // Priority 3: Any goal memory at all
    find_nearest_goal(X, Y).

find_nearest_goal(X, Y) :-
    .findall([math.abs(GX)+math.abs(GY), GX, GY], find_goal(GX, GY), L) & 
    .sort(L, [[_, X, Y]|_]).

teammate_at(GX, GY) :- 
    thing(X, Y, agent, Name) & .substring("connectionA", Name) & 
    .my_name(Me) & Name \== Me & 
    math.abs(GX - X) + math.abs(GY - Y) <= 2. // Radius 2 allows efficient packing.

/* Requirement extraction and carrying check */
extract_req([req(RX,RY,BType)|_], RX, RY, BType).
block_at_req(RX, RY, BType) :- attached(RX, RY) & thing(RX, RY, block, BType).

// -----------------------------------------------------------------------
// COLLECTION gate: checks by TYPE COUNT only (position is irrelevant here).
// A block attaches at the adjacent cell, NOT at the final required position.
// Rotation at the goal aligns blocks. So collect→goal transition uses types.
//
// count_type_in_reqs/3  – how many times Type appears in Reqs
// count_attached_type/2 – how many blocks of Type are attached (any position)
// blocks_collected/1    – true when enough of each type is attached
// -----------------------------------------------------------------------
count_type_in_reqs([], _, 0).
count_type_in_reqs([req(_,_,T)|Rest], T, N) :-
    count_type_in_reqs(Rest, T, N1) & N = N1 + 1.
count_type_in_reqs([req(_,_,T2)|Rest], T, N) :-
    T2 \== T & count_type_in_reqs(Rest, T, N).

// Robust checking: if we see the block (thing) OR we remember attaching it (carrying) - Modified by Member 4
count_attached_type(T, N) :-
    .findall(Dir, (adjacent_dir(AX,AY,Dir) & attached(AX,AY) & (thing(AX,AY,block,T) | carrying(Dir, T))), L) & 
    .length(L, N).

type_satisfied(Type, Reqs) :-
    count_type_in_reqs(Reqs, Type, Need) &
    count_attached_type(Type, Have) &
    Have >= Need.

// blocks_collected(Reqs): collection-phase "done" check (TYPE COUNT, not position).
// Uses a separate all_types_ok/2 helper that always passes the FULL Reqs list
// to type_satisfied, so the needed-count is always computed correctly.
blocks_collected(Reqs) :- all_types_ok(Reqs, Reqs).
all_types_ok([], _).
all_types_ok([req(_,_,Type)|Rest], FullReqs) :-
    type_satisfied(Type, FullReqs) &
    all_types_ok(Rest, FullReqs).

// next_needed_type: first type in Reqs we still need more of.
// Passes the FULL Reqs to type_satisfied so counts are correct.
next_needed_type(Reqs, Type) :- first_unsatisfied(Reqs, Reqs, Type).
first_unsatisfied([req(_,_,Type)|_], FullReqs, Type) :-
    not type_satisfied(Type, FullReqs).
first_unsatisfied([_|Rest], FullReqs, Type) :-
    first_unsatisfied(Rest, FullReqs, Type).

carrying_block(Type) :- attached(X, Y) & thing(X, Y, block, Type). // Modified by Member 4

/* =============================================================================
   Decide action (Prioritizing Collector Actions)
   ============================================================================= */

/* 0. Detect successful submit from PREVIOUS step (blocks removed by server after submit) - Modified by Member 4 */
+!decide_action : my_task(T, _) & lastAction(submit) & lastActionResult(success) <-
    .print(">>> COLLECTOR: Task ", T, " submitted successfully! Notifying coordinator.");
    .send(connectionA1, tell, task_completed(T));
    -my_task(T, _);
    -task_status(T, _);
    -waiting_for_block(_); +waiting_for_block(false);
    -at_dispenser(_); +at_dispenser(none);
    -nav_target(_,_); // Clear old targets
    -last_dist(_);    // Clear distance monitor
    -nav_mode(_); +nav_mode(explore);
    !explore.

/* 1. All blocks collected by type -> Go to Goal and Submit */
// blocks_collected uses TYPE-COUNT check (position-independent).
// all_reqs_satisfied (position check) is the final gate only inside submitting_logic.
+!decide_action : my_task(T, Reqs) & blocks_collected(Reqs) <-
    !submitting_logic(T, Reqs).

/* 2. If carrying block but NO task assigned -> Drop it - Modified by Member 4 */
+!decide_action : carrying_block(_) & not my_task(_, _) <-
    /* Double check no ghost task from coordination delay */
    !do_drop_cooldown.

+!do_drop_cooldown : lastActionResult(success) & (lastAction(detach) | lastAction(rotate)) <-
    /* Just wait for next turn to ensure feedback is processed */
    skip.

+!do_drop_cooldown : true <-
    !drop_all_unnecessary_blocks.

/* 3. Still need blocks -> fetch next required type */
+!decide_action : my_task(T, Reqs) & not blocks_collected(Reqs) & next_needed_type(Reqs, Type) <-
    .print(">>> COLLECTOR: Task ", T, " - fetching next needed block: ", Type);
    !fetching_logic(Type).

/* 3b. Assigned task but cannot work out next type -> explore */
+!decide_action : my_task(T, Reqs) & not blocks_collected(Reqs) <-
    .print(">>> COLLECTOR: Task ", T, " - cannot determine next block, exploring.");
    !explore.



/* 3. Normal Navigation modes (Goto target or Explore) */
+!decide_action : nav_mode(goto) & nav_target(0,0) <-
    .print("skip (reason: navigation target reached)");
    -nav_mode(_); +nav_mode(explore);
    -nav_target(_); -last_dist(_);
    skip.

+!decide_action : nav_mode(goto) & nav_target(Tx,Ty) <-
    !moveToward(Tx,Ty).

+!decide_action : true <-
    !explore.

/* ------------------------------
   Collector State Logic
   ------------------------------ */

// FETCHING: Move to dispenser, request, then attach
// Plan A: Waiting for block after request - try to attach
+!fetching_logic(Type) : waiting_for_block(true) & at_dispenser(Dir) & thing(X, Y, block, Type) & is_adjacent(X, Y, Dir) <-
    .print(">>> COLLECTOR: Block appeared! Attaching at ", Dir);
    -waiting_for_block(_); +waiting_for_block(false);
    -at_dispenser(_); +at_dispenser(none);
    attach(Dir).

// Plan B: Already holding something during fetching phase - Added by Member 4
// If we can't determine the block or it fails, but we ARE full... drop it.
+!fetching_logic(Type) : (lastAction(attach) | lastAction(request)) & not lastActionResult(success) & attached(X, Y) <-
    .print(">>> COLLECTOR: Inventory full (but task fetch continues). Dropping and retrying.");
    !drop_attached_block(X, Y).

// Plan B: Waiting but block not yet visible. - Modified by Member 4
// FIX: Added wait_steps counter. If block doesn't appear within 4 steps, give up.
// Root cause of A3 freeze: request() succeeded (server says OK) but A5 was occupying
// the dispenser cell so the block couldn't materialize. Plan B looped forever.
+!fetching_logic(Type) : waiting_for_block(true) & lastActionResult(success) & wait_steps(W) & W < 4 <-
    .print(">>> COLLECTOR: Waiting for block to appear after request... (", W, "/4)");
    NW = W + 1; -wait_steps(_); +wait_steps(NW);
    skip.

// Plan B-TIMEOUT: Waited too long - block never appeared. Reset and find another dispenser. - Added by Member 4
+!fetching_logic(Type) : waiting_for_block(true) & lastActionResult(success) <-
    .print(">>> COLLECTOR: Block wait TIMEOUT. Dispenser may be blocked by another agent. Resetting.");
    -waiting_for_block(_); +waiting_for_block(false);
    -at_dispenser(_); +at_dispenser(none);
    -wait_steps(_); +wait_steps(0);
    !explore.

// Plan C: Waiting but request did not succeed - reset and retry - Modified by Member 4
+!fetching_logic(Type) : waiting_for_block(true) & not lastActionResult(success) <-
    .print(">>> COLLECTOR: Request failed. Resetting wait state.");
    -waiting_for_block(_); +waiting_for_block(false);
    -at_dispenser(_); +at_dispenser(none);
    !explore.

// Plan D: If a block of the right type is ALREADY adjacent (not attached), just attach it! - Modified by Member 4
// FIX: Added 'not agent_adjacent' to avoid clashing with teammates over the same block.
// COMMENT: We could improve this by 'stealing' blocks if the nearby agent is an opponent.
// For now, we avoid any block with an agent nearby to prevent deadlocks.
+!fetching_logic(Type) : thing(X, Y, block, Type) & is_adjacent(X, Y, Dir) & not attached(X, Y) & 
                         not (thing(AX, AY, agent, _) & math.abs(X-AX) + math.abs(Y-AY) <= 1) <-
    .print(">>> COLLECTOR: Block seen adjacent! Attaching at ", Dir);
    attach(Dir).

// Plan E: If adjacent to dispenser and not waiting, request it
+!fetching_logic(Type) : thing(X, Y, dispenser, Type) & is_adjacent(X, Y, Dir) & waiting_for_block(false) <-
    .print(">>> COLLECTOR: Beside dispenser at ", Dir, ". Requesting block...");
    -waiting_for_block(_); +waiting_for_block(true);
    -at_dispenser(_); +at_dispenser(Dir);
    -wait_steps(_); +wait_steps(0);
    request(Dir).

// Plan F: Move toward a seen block (free block in environment)
+!fetching_logic(Type) : thing(X, Y, block, Type) & not attached(X, Y) <-
    .print(">>> COLLECTOR: Moving toward free block at (", X, ",", Y, ")");
    !moveToward(X, Y).

// Plan G: Move toward nearest known dispenser
+!fetching_logic(Type) : find_nearest_dispenser(Type, X, Y) <-
    .print(">>> COLLECTOR: Moving toward nearest dispenser at (", X, ",", Y, ")");
    !moveToward(X, Y).

// Plan H: Search for dispenser/block
+!fetching_logic(Type) : true <-
    .print(">>> COLLECTOR: Searching for dispenser/block: ", Type);
    !explore.


/* =============================================================================
   Helper Plans for Collector
   ============================================================================= */

// Drop attached block - calculate correct direction for any distance (X, Y)
// FIX: Replaced coordinate-based drop logic with direction-based approach.
// The old code used (X,Y) to pick a direction, then called moveToward as fallback.
// This BROKE for:
//   (a) Non-cardinal/diagonal positions (1,1): no case matched → infinite moveToward loop
//   (b) Chain-end positions (0,4): matched Y>0 → detach(s), which IS correct because
//       detach(s) disconnects the DIRECTLY adjacent block at (0,1), releasing the whole chain.
//       But moveToward fallback was wrong - moving toward (0,4) does nothing when block is attached.
// NEW APPROACH: detect the direction of the DIRECT (adjacent) attachment and detach it.
// If the direct attachment is diagonal or we can't tell, cycle through all 4 directions.

// Try to find and detach the directly-adjacent root block.
// Chains: detaching the root (adjacent) block releases all further blocks in the chain.
// -----------------------------------------------------------------------------
// UNIFIED DETACH LOGIC: Dropping unnecessary or stuck blocks. - Rewritten by Member 4
// -----------------------------------------------------------------------------
+!drop_all_unnecessary_blocks : not attached(_, _) <- true.
/* FIX: Removed recursion to prevent stack overflow/action spam. 
   Agent will drop ONE block per turn. Environment update will trigger next drop. */
+!drop_all_unnecessary_blocks : true <-
    ?attached(X, Y);
    .print(">>> COLLECTOR: No task assigned. Dropping unnecessary block at (", X, ",", Y, ")");
    !drop_any_adjacent.

// Brute-force cardinal detaches. 
// Brute-force cardinal detaches - Modified by Member 4
/* NEW: Aggressive drop that cycles through directions if cardinal checks flicker. */
+!drop_any_adjacent : attached(0,1)  <- detach(s).
+!drop_any_adjacent : attached(0,-1) <- detach(n).
+!drop_any_adjacent : attached(1,0)  <- detach(e).
+!drop_any_adjacent : attached(-1,0) <- detach(w).
+!drop_any_adjacent : rotation_attempts(C) & C < 4 <-
    -rotation_attempts(_); +rotation_attempts(C+1);
    .print(">>> COLLECTOR: Non-cardinal block detected. Rotating to release.");
    rotate(cw).
+!drop_any_adjacent : true <-
    Dirs = [n,s,e,w];
    .random(R); Index = math.floor(R * 4);
    .nth(Index, Dirs, Dir);
    .print(">>> COLLECTOR: Panic Drop (Ghost Attachment). Trying detach at ", Dir);
    -rotation_attempts(_); +rotation_attempts(0); // Reset for next turn
    detach(Dir).

+!drop_attached_block(RX, RY) : is_adjacent(RX, RY, Dir) <- detach(Dir).
+!drop_attached_block(RX, RY) : (attached(X, Y) & is_adjacent(X, Y, Dir)) <-
    .print(">>> COLLECTOR: Block (", RX, ",", RY, ") is diagonal - detaching root at ", Dir);
    detach(Dir).
+!drop_attached_block(_, _) : true <- rotate(cw).
/* =============================================================================
   MEMBER 4: Assembly & Delivery (Ghalya) - Added by Member 4
   ============================================================================= */


// =============================================================================
// SUBMISSION: 1-BLOCK TASKS (Smart Rotation & Map-Edge Aware)
// =============================================================================

// CASE 1: Block is in correct position (RX, RY) -> SUBMIT
+!submitting_logic(T, [req(RX, RY, BType)]) : (goal(0, 0) | thing(0, 0, goal, _)) & attached(RX, RY) & thing(RX, RY, block, BType) & nudge_cooldown(0) <-
    .print(">>> COLLECTOR: Block in position (", RX, ",", RY, "). Submitting task: ", T);
    -rotation_attempts(_); +rotation_attempts(0);
    -spin_cycles(_); +spin_cycles(0);
    submit(T).

// CASE 2: Block is NOT in correct position -> ROTATE using dynamic preference
+!submitting_logic(T, [req(RX, RY, BType)]) : (goal(0, 0) | thing(0, 0, goal, _)) & attached(AX, AY) & (AX \== RX | AY \== RY) & rotation_attempts(C) & C < 4 & nudge_cooldown(0) <-
    ?rotation_dir(Dir);
    NC = C + 1;
    -rotation_attempts(_); +rotation_attempts(NC);
    .print(">>> COLLECTOR: Block at (", AX, ",", AY, ") needs rotation to (", RX, ",", RY, "). Attempt ", NC, "/4 using ", Dir);
    rotate(Dir).

// CASE 3: 4 Rotations failed but we haven't given up on the goal yet -> Nudge to find better spot
+!submitting_logic(T, Reqs) : (goal(0, 0) | thing(0, 0, goal, _)) & rotation_attempts(4) & spin_cycles(SC) & SC < 2 & nudge_cooldown(0) <-
    NSC = SC + 1;
    .print(">>> COLLECTOR: Full rotation cycle failed. Cycle ", NSC, "/2. Nudging to find better goal spot.");
    -rotation_attempts(_); +rotation_attempts(0);
    -spin_cycles(_); +spin_cycles(NSC);
    !try_evacuate_goal.

// CASE 4: Task clearly unsolvable or max retries reached.
+!submitting_logic(T, Reqs) : (goal(0, 0) | thing(0, 0, goal, _)) & rotation_attempts(4) <-
    .print(">>> COLLECTOR: TASK ", T, " is UNSOLVABLE (or path blocked). Abandoning.");
    -rotation_attempts(_); +rotation_attempts(0);
    -spin_cycles(_); +spin_cycles(0);
    -my_task(T, _);
    .send(connectionA1, tell, task_failed(T));
    !drop_all_unnecessary_blocks.

// CASE 5: Not on goal but we know where a goal is → move toward it.
+!submitting_logic(T, Reqs) : find_best_goal(X, Y) & nudge_cooldown(0) <-
    +task_status(T, submitting); 
    .print(">>> COLLECTOR: Moving toward best goal at (", X, ",", Y, ")");
    !moveToward(X, Y).

// CASE 6: Cannot find goal → explore
+!submitting_logic(T, Reqs) : true <-
    .print(">>> COLLECTOR: Searching for goal zone...");
    !explore.

// Specialized helpers for goal wiggling
+!try_evacuate_goal : true <-
    .findall(D, (member(D, [n,s,e,w]) & not cell_blocked_dir(D)), Dirs);
    !execute_available_move(Dirs).

+!execute_available_move([H|_]) <-
    .print(">>> COLLECTOR: Nudging to (", H, ") to clear space.");
    -nudge_cooldown(_); +nudge_cooldown(15);
    move(H).
+!execute_available_move([]) <- skip.

