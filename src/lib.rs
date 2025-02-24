use definitions::GlobalContext;


pub mod beta;
pub mod definitions;
pub mod errors;
pub mod manager;
pub mod parsing;
pub mod typing;
pub mod utils;

/*

// a "static variable" containing our proof system. This is required by WASM.
// functions beginning with the macro #[wasm_bindgen] in this file are usually wrappers around function of the library, but applied to this specific structure
lazy_static! {
    static ref PROOF: Mutex<crate::definitions::GlobalContext> =
        Mutex::new(crate::definitions::GlobalContext::new_with_lib());
}

// ----- wrappers -----

#[wasm_bindgen]
pub fn reset(){
    let mut proof = PROOF.lock().unwrap();
    *proof = GlobalContext::new_with_lib();
}

#[wasm_bindgen]
pub fn get_nb_goals() -> usize {
    let proof = PROOF.lock().unwrap();
    proof.goals.len()
}

#[wasm_bindgen]
pub fn get_current_goal() -> String {
    let proof = PROOF.lock().unwrap();
    match proof.root {
        None => "No more goals".to_string(),
        Some(_) => proof.goal_to_string(proof.goals.len()-1),
    }
}

#[wasm_bindgen]
pub fn send_command(text: &str) -> String {
    let output = send_command_output(text);
    serde_json::to_string(&output).expect("Can't generate JSON")
}

// ----- generic functions -----



pub fn parse(text: &str) -> Result<LambdaTerm, ()> {
    match parsing::parse_lambda(text) {
        Ok(e) => Ok(e),
        Err(_) => Err(()),
    }
}

pub fn get_hypothesis(ctx: &GlobalContext) -> Vec<String> {
    ctx.get_hypothesis()
}

// Print the lambda term of the proof
pub fn debug_root() -> String {
    let proof = PROOF.lock().unwrap();
    match &proof.root {
        None => "Not in proof".to_string(),
        Some(x) => proof.lambda_to_string(x.root),
    }
}

fn goals_to_strings(proof: &GlobalContext) -> Vec<String> {
    let mut res = Vec::new();
    for i in 0..proof.goals.len() {
        res.push(proof.goal_to_string(i));
    }
    res.reverse();
    res
}

// An "output" structure that will be send to the website that contain all relevent informations.
// Note that a command return a String to be printed or an error, but this structure contain also information
// about the state of the machine
#[derive(Serialize, Debug, Clone)]
pub struct Output {
    message: String,
    is_error: bool,
    proof_mode: bool,
    goals: Vec<String>,
    current_goal_hypotheses: Vec<String>,
}

// take a command as a &str, then build an Output structure
fn send_command_output(text: &str) -> Output {
    let parsed = parsing::parse_command(text);
    let mut proof = PROOF.lock().unwrap();
    match parsed {
        Ok(command) => {
            let res = proof.command(command);
            match res {
                Ok(message) => Output {
                    message,
                    is_error: false,
                    proof_mode: proof.root.is_some(),
                    goals: goals_to_strings(&proof),
                    current_goal_hypotheses: get_hypothesis(&proof),
                },
                Err(e) => Output {
                    message: e.to_string(),
                    is_error: true,
                    proof_mode: proof.root.is_some(),
                    goals: goals_to_strings(&proof),
                    current_goal_hypotheses: get_hypothesis(&proof),
                },
            }
        }
        Err(err) => {
            let message = err.to_string();
            Output {
                message,
                is_error: true,
                proof_mode: proof.root.is_some(),
                goals: goals_to_strings(&proof),
                current_goal_hypotheses: get_hypothesis(&proof),
            }
        }
    }
}
*/

pub fn print_comm(proof:&mut GlobalContext,text:&str) {
    match proof.exec_command(text) {
        Ok(e) => println!("{e}"),
        Err(e) => println!("{e}"),
    }
}
pub fn print_comms(proof:&mut GlobalContext,text:&str) {
    match proof.exec_commands(text) {
        Ok(e) => println!("{e}"),
        Err(e) => println!("{e}"),
    }
}
