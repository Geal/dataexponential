extern crate itertools;

use std::fmt;
use std::collections::{HashMap,HashSet};
use itertools::Itertools;

#[derive(Debug,Clone,PartialEq,Hash,Eq)]
pub enum ID {
  Literal(String),
  Variable(String),
}

#[derive(Debug,Clone,PartialEq,Hash,Eq)]
pub struct Predicate {
  pub name: String,
  pub ids: Vec<ID>,
}

#[derive(Debug,Clone,PartialEq)]
pub enum Element {
  Fact(Predicate),
  Rule(Predicate, Vec<Predicate>),
  Query(Predicate),
}

#[derive(Debug,Clone,PartialEq,Hash,Eq)]
pub struct Fact(pub Predicate);

#[derive(Debug,Clone,PartialEq)]
pub struct Rule(pub Predicate, pub Vec<Predicate>);

impl fmt::Display for Fact {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}({:?})", self.0.name, self.0.ids)
  }
}

impl Rule {
  pub fn apply(&self, facts: &HashSet<Fact>, new_facts: &mut Vec<Fact>) {
    let mut variables_set = self.1.iter().flat_map(|pred| pred.ids.iter().filter(|id| {
      match id {
        ID::Variable(_) => true,
        _ => false
      }
    }).map(|id| {
      match id {
        ID::Variable(i) => i.to_string(),
        _ => unreachable!(),
      }
    })).collect::<HashSet<_>>();

    let variables = MatchedVariables::new(variables_set.drain().collect());

    new_facts.extend(CombineIt::new(variables, &self.1, facts).map(|h| {
      let mut p = self.0.clone();
      for index in 0..p.ids.len() {
        let value = match &p.ids[index] {
          ID::Literal(_) => continue,
          ID::Variable(i) => h.get(i).unwrap(),
        };

        p.ids[index] = lit(value);
      }

      Fact(p)
    }));
  }
}

pub struct CombineIt<'a> {
  variables: MatchedVariables,
  predicates: &'a [Predicate],
  all_facts: &'a HashSet<Fact>,
  current_facts: Box<Iterator<Item=&'a Fact> + 'a>,
  current_it: Option<Box<CombineIt<'a>>>,
}

impl<'a> CombineIt<'a> {
  pub fn new(variables: MatchedVariables, predicates: &'a [Predicate], facts: &'a HashSet<Fact>) -> Self {
    let mut p = predicates[0].clone();
    CombineIt {
      variables,
      predicates,
      all_facts: facts,
      current_facts: Box::new(facts.iter().filter(move |fact| match_preds(&fact.0, &p))),
      current_it: None,
    }
  }
}

impl<'a> Iterator for CombineIt<'a> {
  type Item = HashMap<String, String>;

  fn next(&mut self) -> Option<HashMap<String,String>> {
    if self.predicates.is_empty() {
      return self.variables.complete();
    }

    loop {

      if self.current_it.is_none() {
        let pred = &self.predicates[0];

        loop {
          if let Some(current_fact) = self.current_facts.next() {
            let mut vars = self.variables.clone();
            let mut match_ids = true;
            for (key, id) in pred.ids.iter().zip(&current_fact.0.ids) {
              if let (ID::Variable(k), ID::Literal(i)) = (key, id) {
                if !vars.insert(&k, &i) {
                  match_ids = false;
                  break;
                }
              }
            }

            if !match_ids {
              continue;
            }

            if self.predicates.len() == 1 {
              if let Some(val) = vars.complete() {
                return Some(val);
              } else {
                continue;
              }
            } else {
              self.current_it = Some(Box::new(CombineIt::new(vars, &self.predicates[1..], &self.all_facts)));
            }
            break;
          } else {
            return None;
          }
        }
      }

      if self.current_it.is_none() {
        break None;
      }

      if let Some(val) = self.current_it.as_mut().and_then(|it| it.next()) {
        break Some(val);
      } else {
        self.current_it = None;
      }
    }
  }
}

#[derive(Debug,Clone,PartialEq)]
pub struct MatchedVariables(pub HashMap<String, Option<String>>);

impl MatchedVariables {
  pub fn new(import: Vec<String>) -> Self {
    MatchedVariables(import.iter().map(|key| (key.clone(), None)).collect())
  }

  pub fn insert(&mut self, key: &str, value: &str) -> bool {
    match self.0.get(key) {
      Some(None) => {
        self.0.insert(key.to_string(), Some(value.to_string()));
        true
      },
      Some(Some(v)) => value == v.as_str(),
      None => false
    }
  }

  pub fn is_complete(&self) -> bool {
    self.0.iter().all(|(k, v)| v.is_some())
  }

  pub fn complete(&self) -> Option<HashMap<String, String>> {
    if self.0.iter().all(|(k, v)| v.is_some()) {
      Some(self.0.iter().map(|(k, v)| (k.clone(), v.clone().unwrap())).collect())
    } else {
      None
    }
  }
}
pub fn fact(name: &str, ids: &[&str]) -> Fact {
  Fact(Predicate {
    name: name.to_string(),
    ids: ids.iter().map(|id| ID::Literal(id.to_string())).collect(),
  })
}

pub fn pred(name: &str, ids: &[ID]) -> Predicate {
  Predicate {
    name: name.to_string(),
    ids: Vec::from(ids),
  }
}

pub fn rule(head_name: &str, head_ids: &[ID], predicates: &[Predicate]) -> Rule {
  Rule(
    pred(head_name, head_ids),
    Vec::from(predicates)
  )
}

pub fn lit(name: &str) -> ID {
  ID::Literal(name.to_string())
}

pub fn var(name: &str) -> ID {
  ID::Variable(name.to_string())
}

pub fn match_preds(pred1: &Predicate, pred2: &Predicate) -> bool {
  pred1.name == pred2.name &&
    pred1.ids.len() == pred2.ids.len() &&
    pred1.ids.iter().zip(&pred2.ids).all(|(fid, pid)| {
      match (fid, pid) {
        (ID::Literal(_), ID::Variable(_)) => true,
        (ID::Variable(_), ID::Literal(_)) => true,
        (ID::Literal(i), ID::Literal(ref j)) => i == j,
        _ => false
      }
    })

}

#[derive(Debug,Clone,PartialEq)]
pub struct World {
  pub facts: HashSet<Fact>,
  pub rules: Vec<Rule>,
}

impl World {
  pub fn new() -> Self {
    World {
      facts: HashSet::new(),
      rules: Vec::new(),
    }
  }

  pub fn run(&mut self) {
    let mut index = 0;
    loop {
      let mut new_facts:Vec<Fact> = Vec::new();
      for rule in self.rules.iter() {
        rule.apply(&self.facts, &mut new_facts);
        println!("new_facts after applying {:?}:\n{:#?}", rule, new_facts);
      }


      let len = self.facts.len();
      self.facts.extend(new_facts.drain(..));
      if self.facts.len() == len {
        break;
      }

      index+= 1;
      if index == 100 {
        panic!();
      }
    }

  }

  pub fn query(&self, pred: Predicate) -> Option<Vec<&Fact>> {
    let facts = self.facts.iter().filter(|f| {
      &f.0.name == &pred.name &&
          f.0.ids.iter().zip(&pred.ids).all(|(fid, pid)| {
            match (fid, pid) {
              (ID::Literal(_), ID::Variable(_)) => true,
              (ID::Literal(i), ID::Literal(ref j)) => i == j,
              _ => false
            }
          })
      }).collect::<Vec<_>>();

    if facts.is_empty() {
      None
    } else {
      Some(facts)
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn family() {
    let mut w = World::new();
    w.facts.insert(fact("parent", &["A", "B"]));
    w.facts.insert(fact("parent", &["B", "C"]));
    w.facts.insert(fact("parent", &["C", "D"]));
    w.facts.insert(fact("parent", &["C", "E"]));
    w.rules.push(rule("grandparent", &[var("grandparent"), var("grandchild")], &[
      pred("parent", &[var("grandparent"), var("parent")]),
      pred("parent", &[var("parent"), var("grandchild")])
    ]));

    w.run();

    println!("parents:");
    let res = w.query(pred("parent", &[var("parent"), var("grandchild")]));
    for fact in res.unwrap() {
      println!("\t{}", fact);
    }
    println!("parents of B: {:?}", w.query(pred("parent", &[var("parent"), lit("B")])));
    println!("grandparents: {:?}", w.query(pred("grandparent", &[var("grandparent"), var("grandchild")])));

    w.rules.push(rule("siblings", &[var("A"), var("B")], &[
      pred("parent", &[var("parent"), var("A")]),
      pred("parent", &[var("parent"), var("B")])
    ]));

    w.run();
    println!("siblings: {:#?}", w.query(pred("siblings", &[var("A"), var("B")])).unwrap());
    panic!();
  }
}
