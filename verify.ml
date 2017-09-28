(**
 * CSC 208
 * Homework 4: Verification of State Machines
 *)

(* A simple assertion library (don't modify this!) {{{ *)

let run_test (desc:string) (f: unit -> bool) =
  print_endline ("Running: " ^ desc ^ "... ");
  flush_all ();
  try if not (f ()) then
    begin
      print_endline "Test failed!"
    end
  else
    ()
  with e -> print_endline ("Test error: " ^ Printexc.to_string e)

      (* }}} *)

      (*
 * One particularly useful of application of algebraic datatypes is creating
 * programs that embody finite state machines.  A state machine is a model of
 * computation where the behavior of the program is dictated by a finite set
 * of states that the program moves between.  As you will learn in CSC 341,
 * finite state machines have a precise mathematical definition that allows
 * us to be highly precise about how we specify their behavior.  For the
 * purposes of this course, we will prefer to take a more informal view of
 * their construction and save our formality for proofs of their correctness.
 *
 * For this homework, you will need to (a) fill out the definitions in this
 * file and (b) create a PDF for the non-programming questions described in
 * this file.  Make sure to submit:
 *
 * 1. The completed source files,
 * 2. A PDF of your written, non-programming answers, and
 * 3. The .tex source of your PDF
 *
 * By the deadline.
 *
 * This homework is broken up into two parts.  Your submission should include
 * both completed source files.  Your singular write-up should contain answers
 * to the questions posed in both parts.
       *)

      (***** Problem 1 (Traffic Lights) ********************************************)

      (*
 * The beauty of finite state machines is that they can be used to model a
 * wide variety of phenomena.  For example, a finite state machine can be
 * used to describe the behavior of a system of traffic lights.  In OCaml,
 * we can build a program that models this behavior by first constructing a
 * an ADT that describes the possible states of a traffic light.  For our
 * purposes, a traffic light can be either green (go), yellow (caution), and
 * red (stop):
       *)

type light =
  | Green
  | Yellow
  | Red

      (*
 * A four-way intersection typically has one light for each incoming road.
 * However, on many intersections, the behavior of the lights across from each
 * other are symmetric.  That is, consider the following intersection:
 *
 *     A
 *     |
 * D ===== B
 *     |
 *     C
 *
 * Because A and C are opposite each other, it is fine if both their lights are
 * green, so they will typically be in sync, likewise with D and B.  However,
 * it would be problematic if A and B's lights were synced because then cars
 * driving from A and B might collide into each other.
 *
 * Because of this, we will model an intersection as a pair of lights with the
 * idea that each light represents parallel intersections, i.e., A and C or
 * B and D.  On top of this, when both lights become red, we need to know which
 * of the two sets of lights should become green.  Therefore, we need to also
 * include a boolean value in our intersection type that tells us which
 * intersection becomes green once both lights become red.
       *)

type intersection = light * light * bool

      (*
 * Note that we can use the type keyword to create a type alias as well as
 * an algebraic data type.  In this case, intersection is a short-hand for
 * the type of a triple of lights and a boolean analogous to a typedef
 * declaration in C.
       *)

      (*
 * With these type definitions in place, we can now write a function that
 * simulates an intersection.  The heart of the simulation is a function
 * that takes the current state that we're in and produces the new state.
       *)

let advance_intersection (i:intersection) : intersection =
  match i with
  | (Green, Red, b)   -> (Yellow, Red, b)
  | (Yellow, Red, b)  -> (Red, Red, not b)
  | (Red, Red, false) -> (Red, Green, true)
  | (Red, Green, b)   -> (Red, Yellow, b)
  | (Red, Yellow, b)  -> (Red, Red, not b)
  | (Red, Red, true)  -> (Green, Red, false)
  | (l1, l2, b)       -> (l1, l2, b)

        (*
 * Part (a): first, play around with this function to understand how it works.
 * Fill in the following test cases to codify that understanding.
         *)

let test () : bool =
  advance_intersection (Green, Green, true) = (Green, Green, true)
;; run_test "advance_intersection: testing the 'other' (l1, l2, b) should return the same thing" test

let test () : bool =
  advance_intersection (Red, Red, true) = (Green, Red, false)
;; run_test "advance_intersection: the intersection (Red, Red, true) should return (Green, Red, false)" test

(*
 * Part (b): a properly working intersection does not give right-of-way to
 * perpendicular lights.  We'll call such an intersection consistent.
 * An inconsistent intersection is one that gives right-of-way to perpendicular
 * lights.  Write a function, intersection_consistent, that returns true iff
 * the intersection is consistent, as well as associated test cases that
 * show that your implementation works:
 *)

let intersection_consistent (i:intersection) : bool =
  let (light1, light2, b) = i in
  if light1 = Red || light2 = Red
  then true
      else false

let test () : bool =
  intersection_consistent (Green, Yellow, false) = false
;; run_test "intersection_consistent: any intersection without Red will return false " test

let test () : bool =
  intersection_consistent (Red, Green, false) = true
;; run_test "intersection_consistent: a consistent intersection will have a red light, this one has a red light so it's true" test

(*
 * Part (c): we would like to eventually prove that advance_intersection only
 * produces consistent results.  However, it is not always the case that this
 * is true.  Show this by proving the following claim:
 *
 * Claim 1c: There exists an intersection i such that
 *           intersection_consistent (advance_intersection i) = false.
 *)

(*
 * Part (d): what pre-condition do you need on advance_intersection to guarantee
 * that advance_intersection always produces a consistent result?  Write the
 * condition formally P(i) as a function of an arbitrary intersection.
 *)

(*
 * Part (e): with the precondition P(i) that you identified in the previous
 * part, finally prove the correctness of advance_intersection:
 *
 * Claim 1e: For all intersections i,
 *   P(i) -> intersection_consistent (advance_intersection i) = true.
 *)

(***** Problem 2 (Server) ****************************************************)

(*
 * Another example of a finite state machine is a server-style program that
 * hosts data, public and private.  The server allows users to optionally
 * authenticate after connecting to enable them to read private data in
 * addition to public data.  While we would need to appeal to networking and
 * database libraries to properly implement such a server, we can emulate the
 * authentication portion of the system with the language constructs we've seen
 * so far.
 *)

(*
 * First we'll define the series of commands we can issue to the server as an
 * algebraic datatype.
 *)

type command =
  | Connect
  | ReadPublic
  | Authenticate
  | ReadPrivate
  | Disconnect

      (*
 * Next we'll formalize the rules of the server:
 *
 * 1. A user must connect before reading or authenticating to the server.
 * 2. A user must authenticate before reading private data.
 * 3. A user must disconnect to end the session.
 *
 * The state of a session then consists of two parts: whether a client is
 * connected to the server and whether the client is authenticated.  We'll
 * represent this with a pair of booleans.
       *)

type server_state = bool * bool   (* connected, authenticated *)


      (*
 * And now, we'll present a candidate implementation of this protocol which is
 * a function that takes the current server state and a command and returns
 * the updated state:
       *)

let process_command (st:server_state) (cmd:command) : server_state =
  let (connected, authenticated) = st in
  match cmd with
  | Connect ->
      if connected then begin
        print_endline "Connected";
        (true, authenticated)
      end else
        failwith "Tried to connect but already connected"
  | ReadPublic ->
      if connected then begin
        print_endline "Reading public data";
        (connected, authenticated)
      end else
        failwith "Tried to read before connecting"
  | Authenticate ->
      if connected && not authenticated then begin
        print_endline "Authenticated";
        (connected, true)
      end else if not connected then
        failwith "Tried to authenticate before connecting"
      else
        failwith "Tried to authenticate but already authenticated"
  | ReadPrivate ->
      if connected && authenticated then begin
        print_endline "Read private data";
        (connected, authenticated)
      end else if not connected then
        failwith "Tried to read before connecting"
      else
        failwith "Tried to read private data before authenticating"
  | Disconnect ->
      if not connected then begin
        print_endline "Disconnected";
        (false, authenticated)
      end else
        failwith "Tried to disconnect but not connected"

          (*
 * In the implementation, I used a few new OCaml features that we haven't seen
 * before:
 *
 *   + The print_endline function prints a string to the console.  The
 *     function has type string -> unit where unit is the type with a single
 *     value `()`.  We typically use `()` as the return type of a function that
 *     produces a side-effect and returns nothing as a result.
 *   + We can sequence together expressions with the semicolon operator, `;`.
 *     `e1 ; e2` evaluates e1, discards the result and goes on to evaluate e2
 *     and produce its value as the overall value of the operator.  The
 *     semicolon operator is more commonly known as the expression composition
 *     operator as a result.
 *   + `begin .. end` simply serve as parentheses, literally.  They are a more
 *     readable alternative to `(` and `)` in OCaml.  Typically, I will use
 *     `begin .. end` in conjunction with functions that produce side-effects
 *     such as print_endline to sequence expressions.l
           *)

          (*
 * Part (a): our correctness condition for this server is that the three rules
 * of the server outlined above are fulfilled.  In particular, we'll focus on
 * the second property: a user cannot read private data without first
 * authenticating to the server.  Test the function above and convince yourself
 * that the function works, demonstrating how the function works by filling in
 * the test cases below:
           *)

let test () : bool =
  process_command (true, true)(ReadPrivate) = (true, true)
;; run_test "process_command: ReadPrivate is allowed when both bools of server_state are true..." test

let test () : bool =
   process_command (true, false)(ReadPrivate) =  failwith "Tried to read private data before authenticating"
;; run_test "process_command: ReadPrivate isn't allowed unless the server_state is authenticated..." test

(*
 * Part (b): ...just joking!  If you didn't see already, it turns out there is
 * a serious flaw in our implementation of the server protocol.  Prove the
 * following claim:
 *
 * Claim 2b: there exists a sequence of commands c1, .., ck such that they
 * allow a user to read private data from the server without authenticating.
 *)

(*
 * Part (c): correct the problem in process_command as a new function
 * process_command' below.  You can simply copy-paste the definition of
 * process_command above into the implementation below and then make the
 * necessary changes to the code.  Fill in the tests that demonstrate that your
 * fix works.
 *)

let process_command' (st:server_state) (cmd:command) : server_state =
  let (connected, authenticated) = st in
  match cmd with
  | Connect ->
      if connected then begin
        print_endline "Connected";
        (true, authenticated)
      end else
        failwith "Tried to connect but already connected"
  | ReadPublic ->
      if connected then begin
        print_endline "Reading public data";
        (connected, authenticated)
      end else
        failwith "Tried to read before connecting"
  | Authenticate ->
      if connected && not authenticated then begin
        print_endline "Authenticated";
        (connected, true)
      end else if not connected then
        failwith "Tried to authenticate before connecting"
      else
        failwith "Tried to authenticate but already authenticated"
  | ReadPrivate ->
      if connected && authenticated then begin
        print_endline "Read private data";
        (connected, authenticated)
      end else if not connected then
        failwith "Tried to read before connecting"
      else
        failwith "Tried to read private data before authenticating"
  | Disconnect ->
      if not connected then begin
        print_endline "Disconnected";
        (false, false)
      end else
                failwith "Tried to disconnect but not connected"

let test () : bool =
  process_command' (false, true)(Disconnect) = (false, false)
;; run_test "process_command':if server_state is (false, true), Disconnect should deauthenticate and return (false, false)" test

let test () : bool =
  process_command' (true, false)(ReadPrivate) = failwith "Tried to read private data before authenticating"
;; run_test "process_command': ReadPrivate is not allowed unless st is authenticated" test

(*
 * Part (d): state an appropriate formal claim of correctness of
 * process_command' with respect to the second property of the server and
 * give a formal proof of that claim's correctness.  You should formulate your
 * claim in terms of a single arbitrary command c.
 *)
