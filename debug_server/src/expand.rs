use std::collections::VecDeque;

use serde::Serialize;

/// Program location. Exit is a graph marker, not an instruction index.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Loc {
    Pos(u32),
    Exit,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Dir {
    Only,
    Taken,
    NotTaken,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Status {
    Running,
    Complete,
    Fail,
}

struct Node {
    loc: Loc,
    r: u32,
    preds: Vec<u32>,
    x: i32,
    y: i32,
    depth: u32,
}

struct Edge {
    src: u32,
    dst: u32,
    dir: Dir,
}

struct LogEntry {
    t: u32,
    msg: String,
}

struct Cand {
    dir: Dir,
    loc: Loc,
    r: u32,
}

pub struct Session {
    id: String,
    status: Status,
    reason: Option<String>,
    fuel: u32,
    budget: u32,
    work: VecDeque<u32>,
    focus: u32,
    nodes: Vec<Node>,
    edges: Vec<Edge>,
    log: Vec<LogEntry>,
    cursor_j: u32,
    tick: u32,
}

const INSN_TEXT: [&str; 4] = [
    "if r >= 3 then 3 else 1",
    "r := r + 1",
    "goto 0",
    "return observe r",
];

impl Session {
    pub fn new(id: impl Into<String>, budget: u32) -> Self {
        let mut session = Self {
            id: id.into(),
            status: Status::Running,
            reason: None,
            fuel: budget,
            budget,
            work: VecDeque::from([0]),
            focus: 0,
            nodes: vec![Node {
                loc: Loc::Pos(0),
                r: 0,
                preds: Vec::new(),
                x: 0,
                y: 0,
                depth: 0,
            }],
            edges: Vec::new(),
            log: Vec::new(),
            cursor_j: 0,
            tick: 0,
        };
        session.push_log("init root at pos 0, r=0");
        session
    }

    pub fn run_all(&mut self) {
        while self.status == Status::Running {
            self.step_once();
        }
    }

    /// One loop iteration of §16 Expand.
    ///
    /// Work is checked before fuel. A step that empties Work reports Complete
    /// in this response, including when fuel lands on 0. That is the next loop
    /// head, so the client does not send a blank extra step.
    pub fn step_once(&mut self) {
        if self.status != Status::Running {
            return;
        }
        if self.work.is_empty() {
            self.mark_complete(None);
            return;
        }
        if self.fuel == 0 {
            self.mark_fail("LimitExceeded");
            return;
        }

        let eta = self.work.pop_front().expect("work non-empty");
        self.fuel -= 1;
        let parent = &self.nodes[eta as usize];
        let parent_x = parent.x;
        let parent_depth = parent.depth;
        let parent_loc = parent.loc;
        let parent_r = parent.r;
        let stepped_pos = match parent_loc {
            Loc::Pos(j) => j,
            Loc::Exit => {
                self.mark_fail("StepOnExit");
                return;
            }
        };

        let prepared = match demo_step(parent_loc, parent_r) {
            Ok(cands) => cands,
            Err(reason) => {
                self.mark_fail(reason);
                return;
            }
        };

        let count = prepared.len();
        for (index, cand) in prepared.into_iter().enumerate() {
            let zeta = self.nodes.len() as u32;
            let depth = parent_depth + 1;
            self.nodes.push(Node {
                loc: cand.loc,
                r: cand.r,
                preds: vec![eta],
                x: child_x(parent_x, index, count),
                y: depth as i32 * 100,
                depth,
            });
            self.edges.push(Edge {
                src: eta,
                dst: zeta,
                dir: cand.dir,
            });
            if cand.loc != Loc::Exit {
                self.work.push_back(zeta);
            }
            self.push_log(format!(
                "expand node {eta} pos {stepped_pos} r={parent_r} {} -> node {zeta} loc {} r={}",
                dir_name(cand.dir),
                loc_name(cand.loc),
                cand.r
            ));
        }

        if self.work.is_empty() {
            self.mark_complete(Some(stepped_pos));
        } else if let Some(&head) = self.work.front() {
            self.focus_node(head);
        }
    }

    pub fn snapshot(&self) -> Snapshot {
        Snapshot {
            id: self.id.clone(),
            status: match self.status {
                Status::Running => "running",
                Status::Complete => "complete",
                Status::Fail => "fail",
            },
            reason: self.reason.clone(),
            fuel: self.fuel,
            budget: self.budget,
            work: self.work.iter().copied().collect(),
            focus: self.focus,
            insns: INSN_TEXT
                .iter()
                .enumerate()
                .map(|(j, text)| InsnOut {
                    j: j as u32,
                    text,
                })
                .collect(),
            nodes: self
                .nodes
                .iter()
                .enumerate()
                .map(|(id, node)| NodeOut {
                    id: id as u32,
                    loc: loc_name(node.loc).to_string(),
                    r: node.r,
                    preds: node.preds.clone(),
                    x: node.x,
                    y: node.y,
                })
                .collect(),
            edges: self
                .edges
                .iter()
                .map(|edge| EdgeOut {
                    src: edge.src,
                    dst: edge.dst,
                    dir: dir_name(edge.dir),
                })
                .collect(),
            log: self
                .log
                .iter()
                .map(|entry| LogOut {
                    t: entry.t,
                    msg: entry.msg.clone(),
                })
                .collect(),
            cursor_j: self.cursor_j,
        }
    }

    fn focus_node(&mut self, id: u32) {
        self.focus = id;
        if let Loc::Pos(j) = self.nodes[id as usize].loc {
            self.cursor_j = j;
        }
    }

    fn mark_complete(&mut self, stepped_pos: Option<u32>) {
        self.status = Status::Complete;
        self.reason = None;
        if let Some(j) = stepped_pos {
            self.cursor_j = j;
        }
        if let Some(id) = self
            .nodes
            .iter()
            .enumerate()
            .rev()
            .find(|(_, node)| node.loc == Loc::Exit)
            .map(|(id, _)| id as u32)
        {
            self.focus = id;
        }
        self.push_log("complete");
    }

    fn mark_fail(&mut self, reason: &str) {
        self.status = Status::Fail;
        self.reason = Some(reason.to_string());
        self.push_log(format!("fail {reason}"));
    }

    fn push_log(&mut self, msg: impl Into<String>) {
        let t = self.tick;
        self.tick += 1;
        self.log.push(LogEntry { t, msg: msg.into() });
    }
}

fn demo_step(loc: Loc, r: u32) -> Result<Vec<Cand>, &'static str> {
    let Loc::Pos(j) = loc else {
        return Err("StepOnExit");
    };
    match j {
        0 if r >= 3 => Ok(vec![Cand {
            dir: Dir::Taken,
            loc: Loc::Pos(3),
            r,
        }]),
        0 => Ok(vec![Cand {
            dir: Dir::NotTaken,
            loc: Loc::Pos(1),
            r,
        }]),
        1 => Ok(vec![Cand {
            dir: Dir::Only,
            loc: Loc::Pos(2),
            r: r + 1,
        }]),
        2 => Ok(vec![Cand {
            dir: Dir::Only,
            loc: Loc::Pos(0),
            r,
        }]),
        3 => Ok(vec![Cand {
            dir: Dir::Only,
            loc: Loc::Exit,
            r,
        }]),
        _ => Err("InvalidTarget"),
    }
}

fn child_x(parent_x: i32, index: usize, count: usize) -> i32 {
    if count <= 1 {
        return parent_x;
    }
    let span = 180;
    let mid = (count as i32 - 1) * span / 2;
    parent_x - mid + index as i32 * span
}

fn loc_name(loc: Loc) -> &'static str {
    match loc {
        Loc::Pos(0) => "0",
        Loc::Pos(1) => "1",
        Loc::Pos(2) => "2",
        Loc::Pos(3) => "3",
        Loc::Pos(_) => "?",
        Loc::Exit => "exit",
    }
}

fn dir_name(dir: Dir) -> &'static str {
    match dir {
        Dir::Only => "only",
        Dir::Taken => "taken",
        Dir::NotTaken => "not_taken",
    }
}

#[derive(Serialize)]
pub struct Snapshot {
    pub id: String,
    pub status: &'static str,
    pub reason: Option<String>,
    pub fuel: u32,
    pub budget: u32,
    pub work: Vec<u32>,
    pub focus: u32,
    pub insns: Vec<InsnOut>,
    pub nodes: Vec<NodeOut>,
    pub edges: Vec<EdgeOut>,
    pub log: Vec<LogOut>,
    pub cursor_j: u32,
}

#[derive(Serialize)]
pub struct InsnOut {
    pub j: u32,
    pub text: &'static str,
}

#[derive(Serialize)]
pub struct NodeOut {
    pub id: u32,
    pub loc: String,
    pub r: u32,
    pub preds: Vec<u32>,
    pub x: i32,
    pub y: i32,
}

#[derive(Serialize)]
pub struct EdgeOut {
    #[serde(rename = "from")]
    pub src: u32,
    #[serde(rename = "to")]
    pub dst: u32,
    pub dir: &'static str,
}

#[derive(Serialize)]
pub struct LogOut {
    pub t: u32,
    pub msg: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn locs(session: &Session) -> Vec<(u32, &'static str, u32, i32, i32)> {
        session
            .nodes
            .iter()
            .enumerate()
            .map(|(id, node)| (id as u32, loc_name(node.loc), node.r, node.x, node.y))
            .collect()
    }

    fn edges(session: &Session) -> Vec<(u32, &'static str, u32)> {
        session
            .edges
            .iter()
            .map(|edge| (edge.src, dir_name(edge.dir), edge.dst))
            .collect()
    }

    #[test]
    fn fresh_session_matches_the_root_snapshot() {
        let session = Session::new("s", 11);
        let snap = session.snapshot();
        assert_eq!(snap.status, "running");
        assert_eq!(snap.reason, None);
        assert_eq!(snap.fuel, 11);
        assert_eq!(snap.budget, 11);
        assert_eq!(snap.work, vec![0]);
        assert_eq!(snap.focus, 0);
        assert_eq!(snap.cursor_j, 0);
        assert_eq!(snap.nodes.len(), 1);
        assert_eq!(snap.nodes[0].loc, "0");
        assert_eq!(snap.nodes[0].r, 0);
        assert_eq!(snap.edges.len(), 0);
        assert_eq!(snap.log[0].t, 0);
        assert_eq!(snap.log[0].msg, "init root at pos 0, r=0");
        assert_eq!(snap.insns[0].text, "if r >= 3 then 3 else 1");
        assert_eq!(snap.insns[3].text, "return observe r");
    }

    #[test]
    fn budget_11_run_matches_section_18() {
        let mut session = Session::new("s", 11);
        session.run_all();
        let snap = session.snapshot();
        assert_eq!(snap.status, "complete");
        assert_eq!(snap.reason, None);
        assert_eq!(snap.fuel, 0);
        assert_eq!(snap.work, Vec::<u32>::new());
        assert_eq!(snap.focus, 11);
        assert_eq!(snap.cursor_j, 3);
        assert_eq!(
            locs(&session),
            vec![
                (0, "0", 0, 0, 0),
                (1, "1", 0, 0, 100),
                (2, "2", 1, 0, 200),
                (3, "0", 1, 0, 300),
                (4, "1", 1, 0, 400),
                (5, "2", 2, 0, 500),
                (6, "0", 2, 0, 600),
                (7, "1", 2, 0, 700),
                (8, "2", 3, 0, 800),
                (9, "0", 3, 0, 900),
                (10, "3", 3, 0, 1000),
                (11, "exit", 3, 0, 1100),
            ]
        );
        assert_eq!(
            edges(&session),
            vec![
                (0, "not_taken", 1),
                (1, "only", 2),
                (2, "only", 3),
                (3, "not_taken", 4),
                (4, "only", 5),
                (5, "only", 6),
                (6, "not_taken", 7),
                (7, "only", 8),
                (8, "only", 9),
                (9, "taken", 10),
                (10, "only", 11),
            ]
        );
        assert!(snap.nodes.iter().any(|node| node.loc == "exit"));
        assert_eq!(snap.log.last().map(|entry| entry.msg.as_str()), Some("complete"));
    }

    #[test]
    fn budget_10_stops_before_the_return() {
        let mut session = Session::new("s", 10);
        session.run_all();
        let snap = session.snapshot();
        assert_eq!(snap.status, "fail");
        assert_eq!(snap.reason.as_deref(), Some("LimitExceeded"));
        assert_eq!(snap.fuel, 0);
        assert_eq!(snap.work, vec![10]);
        assert_eq!(snap.focus, 10);
        assert_eq!(snap.cursor_j, 3);
        assert_eq!(snap.nodes.len(), 11);
        assert!(snap.nodes.iter().all(|node| node.loc != "exit"));
        assert_eq!(snap.nodes[10].loc, "3");
        assert_eq!(snap.nodes[10].r, 3);
    }

    #[test]
    fn zero_fuel_fails_without_popping_work() {
        let mut session = Session::new("s", 0);
        session.step_once();
        let snap = session.snapshot();
        assert_eq!(snap.status, "fail");
        assert_eq!(snap.reason.as_deref(), Some("LimitExceeded"));
        assert_eq!(snap.work, vec![0]);
        assert_eq!(snap.nodes.len(), 1);
        assert_eq!(snap.fuel, 0);
    }

    #[test]
    fn one_step_enqueues_the_not_taken_child() {
        let mut session = Session::new("s", 11);
        session.step_once();
        let snap = session.snapshot();
        assert_eq!(snap.status, "running");
        assert_eq!(snap.fuel, 10);
        assert_eq!(snap.work, vec![1]);
        assert_eq!(snap.focus, 1);
        assert_eq!(snap.cursor_j, 1);
        assert_eq!(snap.edges[0].src, 0);
        assert_eq!(snap.edges[0].dst, 1);
        assert_eq!(snap.edges[0].dir, "not_taken");
        assert_eq!(snap.nodes[1].loc, "1");
        assert_eq!(snap.nodes[1].r, 0);
        assert_eq!(snap.nodes[1].preds, vec![0]);
    }
}
