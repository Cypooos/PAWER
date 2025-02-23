# `pawer_core`

A rust library to work with the Calculus of Construction. Made for the PAWER (Proof Assistant Web Embeded in Rust) project.

The original project is at `https://gitlab.aliens-lyon.fr/pawer/pawer_core` but is severly outdated

## Usage

Be sure to have cargo installed !
You can do `cargo run` to start a simple console version of the tool.
You can run the tests using `cargo test`

## Documentation
You can generate the documentation of the library by using the `make doc` command (it's an alias for `cargo doc --lib --open`).
The file will be generated under `./target/doc/pawer_core/index.html`

## Commands

Generic commands:
- *Check*: `Check <lambda>.` tries to type `<lambda>` and prints the output.
- *Reduce*: `Reduce <lambda>.` reduce to a beta normal-form the `lambda`. Alias: `Compute <lambda>.`
- *Search*: `Search <string>.` search in the list of defined contants / inductive types the ones that contains `<string>`.
            If `<string>` is empty, returns all defined function / types.
- *Print*: `Print <lambda>.` print `<lambda>` (will remove syntaxic sugar) 
- *PrintProof*: `PrintProof.` will print the current lambda-term of the proof, with hole if they are some.
- *Cancel*: `Cancel.` will cancel the current proof.

Commands abouts constants:
- *Goal*: `Goal <prop>.` will start a new proof of `<prop>`. Upon completion, nothing will happen. 
- *Theorem*: `Theorem <name> : <prop>.` will start a new proof of `<prop>`. Upon completion, the theorem wil be added to the constant to be used, under the name `<name>`.
- *Definition*: `Definition <name> : <lambda>.` will try to type `<lambda>`. If sucessful, it will add `<lambda>` to the constants under the name `<name>`.
                It is the same as doing `Theorem <name> : <type>. exact <lambda>. Qed.`
- *Qed*: `Qed.` is used to finish a proof. Will calculate the beta normal-form, and then tries to type the term.
- *Inductive*: `Inductive name (arg1:type1) ... (argN:typeN) : arity := <list of constructor>.` will define an inductive type. 
- *Fixpoint*: `Fixpoint name (arg1:type1) ... (argN:typeN) {struct <struct>} : <type> := <code>` is syntaxic sugar for
                `Definition <name> := fix <name> (arg1:type1) ... (argN:typeN) {struct <struct>} : <type> := <code>`

Tactics:
- *Apply*: `apply <lambda>.` if `<lambda>: A1 -> ... -> AN -> Goal`, will ask for a proof of `A1`, ..., `AN`
- *Exact*: `exact <lambda>.` will try to solve the goal by using the term `<lambda>` directly
- *Cut*: `cut <prop>.` will split the goal in two subgoals: proving `<prop>` and `<prop> -> Goal`
- *Intro*: `intro <name>.` on a goal of the form `A -> B` or `forall x:A, B` with intro either an hypothesis or an element named `<name>`. 
                The `<name>` can be ommited, and the prover will generate a proper unused name.
- *Intros*: `intros <name1> <name2> ... <nameN>.` will perform multiple `intro`. If no name were given, it will do as many intro as possible, generating brand new name for each. 
- *Unfold*: `unfold <name>.` will unfold a constant in the goal and every hypothesis.
- *Simpl*: `simpl.` will beta reduce the goal.
- *Induction*: `induction <var>.` if `<var>:<inductive>:Set`, will perform a proof by induction on the goal. *It is still very buggy and might not work /!\\*

## Project structure and codebase informations

We used the `pest` crate for the parsing. The pest grammar file can be seen in `pest/grammar.pest`. We do not have an incremental parsing.

There is two version of the lambda-terms:
 - The `LambdaTerm` are a tree-like way to represent lambda, used only for parsing reasons.
 - The `LambdaNode` are store in an array, with the 'pointors' that are an index to the next elements.
    This will allow of optimisations (hash-consing) and a memoized version of the beta-reduction
 
The """standard library""" is loaded at the function `utils::load_prelude`. The code used for the showcase can be seen in `presentation.v`

## Status
The project devellopement will be considerably slow down, but Coda B is still looking at hosting a version of it on her website.  

## License
MIT -- see the LICENCE file