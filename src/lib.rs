#![cfg_attr(feature = "unstable", feature(test))]
#[cfg(all(feature = "unstable", test))]
extern crate test;

use std::fmt;
use std::collections::{HashMap,HashSet};

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
    let variables_set = self.1.iter().flat_map(|pred| pred.ids.iter().filter(|id| {
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

    let variables = MatchedVariables::new(variables_set);

    new_facts.extend(CombineIt::new(variables, &self.1, facts).map(|h| {
    //new_facts.extend(Combiner::new(variables, &self.1, facts).map(|h| {
      let mut p = self.0.clone();
      for index in 0..p.ids.len() {
        let value = match &p.ids[index] {
          ID::Variable(i) => h.get(i).unwrap(),
          _ => continue,
        };

        p.ids[index] = value.clone();
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
    let p = predicates[0].clone();
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
  type Item = HashMap<String, ID>;

  fn next(&mut self) -> Option<HashMap<String,ID>> {
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
              if let (ID::Variable(k), id) = (key, id) {
                if !vars.insert(&k, &id) {
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

pub struct Combiner<'a> {
  variables: MatchedVariables,
  predicates: &'a [Predicate],
  pred_facts: Vec<Vec<&'a Fact>>,
  indexes: Vec<usize>,
}

impl<'a> Combiner<'a> {
  pub fn new(variables: MatchedVariables, predicates: &'a [Predicate], facts: &'a HashSet<Fact>) -> Self {
    let pred_facts:Vec<Vec<&Fact>> = predicates.iter().map(|p| {
        facts.iter().filter(move |fact| match_preds(&fact.0, &p)).collect()
      }).collect();
    let indexes = std::iter::repeat(0).take(pred_facts.len()).collect();

    Combiner {
      variables,
      predicates,
      pred_facts,
      indexes,
    }
  }
}

pub fn advance(pred_facts: &[Vec<&Fact>], indexes: &mut[usize]) -> bool {
  let mut cursor = 0;
  //let mut count = 0;
  loop {
    //count += 1;
    //assert!(count < 1000);
    //println!("advance loop(cursor = {}): {:?}", cursor, indexes);

    if cursor == pred_facts.len() {
      return false;
    }

    indexes[cursor] += 1;
    if indexes[cursor] < pred_facts[cursor].len() {
      for i in 0..cursor {
        indexes[i] = 0;
      }
      return true;
    } else {
      cursor += 1;
    }
  }
}

pub fn can_advance(pred_facts: &[Vec<&Fact>], indexes: &[usize]) -> bool {
  indexes.iter().zip(pred_facts).all(|(index, facts)| *index < facts.len())
}

impl<'a> Iterator for Combiner<'a> {
  type Item = HashMap<String, ID>;

  fn next(&mut self) -> Option<HashMap<String,ID>> {
    //println!("Combiner::next(): {:?}, max = {:?}", self.indexes,
    //  self.pred_facts.iter().map(|f| f.len()).collect::<Vec<_>>());

    if self.pred_facts.iter().any(|facts| facts.is_empty()) {
      return None;
    }

    //let mut count = 0;
    loop {
      //count += 1;
      //assert!(count < 100);
      //println!("combiner loop indexes: {:?}", self.indexes);

      if !can_advance(&self.pred_facts, &self.indexes) {
        //println!("cannot advance anymore");
        return None;
      }

      let facts_combination = self.pred_facts.iter().zip(&self.indexes).map(|(facts, index)| facts[*index]);
      let mut vars = self.variables.clone();
      let mut match_ids = true;
      for (key, id) in self.predicates.iter().zip(facts_combination).flat_map(|(pred, fact)| {
        pred.ids.iter().zip(&fact.0.ids)
      }) {
        if let (ID::Variable(k), id) = (key, id) {
          if !vars.insert(&k, &id) {
            match_ids = false;
            break;
          }
        }
      }

      advance(&self.pred_facts, &mut self.indexes);

      if !match_ids {
        continue;
      } else {
        if let Some(v) = vars.complete() {
          //println!("combiner returning: {:?}", v);
          return Some(v);
        }
      }
    }
  }
}

#[derive(Debug,Clone,PartialEq)]
pub struct MatchedVariables(pub HashMap<String, Option<ID>>);

impl MatchedVariables {
  pub fn new(import: HashSet<String>) -> Self {
    MatchedVariables(import.iter().map(|key| (key.clone(), None)).collect())
  }

  pub fn insert(&mut self, key: &str, value: &ID) -> bool {
    match self.0.get(key) {
      Some(None) => {
        self.0.insert(key.to_string(), Some(value.clone()));
        true
      },
      Some(Some(v)) => value == v,
      None => false
    }
  }

  pub fn is_complete(&self) -> bool {
    self.0.values().all(|v| v.is_some())
  }

  pub fn complete(&self) -> Option<HashMap<String, ID>> {
    if self.is_complete() {
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
        (_, ID::Variable(_)) => true,
        (ID::Variable(_), _) => true,
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
        //println!("new_facts after applying {:?}:\n{:#?}", rule, new_facts);
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

  pub fn query(&self, pred: Predicate) -> Vec<&Fact> {
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

    facts
  }

  pub fn query_rule(&self, rule: Rule) -> Vec<Fact> {
    let mut new_facts:Vec<Fact> = Vec::new();
    rule.apply(&self.facts, &mut new_facts);
    new_facts
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

    let query_rule_result = w.query_rule(rule("grandparent", &[var("grandparent"), var("grandchild")], &[
      pred("parent", &[var("grandparent"), var("parent")]),
      pred("parent", &[var("parent"), var("grandchild")])
    ]));
    println!("grandparents query_rules: {:?}", query_rule_result);
    println!("current facts: {:?}", w.facts);

    w.rules.push(rule("grandparent", &[var("grandparent"), var("grandchild")], &[
      pred("parent", &[var("grandparent"), var("parent")]),
      pred("parent", &[var("parent"), var("grandchild")])
    ]));

    w.run();

    println!("parents:");
    let res = w.query(pred("parent", &[var("parent"), var("child")]));
    for fact in res {
      println!("\t{}", fact);
    }
    println!("parents of B: {:?}", w.query(pred("parent", &[var("parent"), lit("B")])));
    println!("grandparents: {:?}", w.query(pred("grandparent", &[var("grandparent"), var("grandchild")])));
    w.facts.insert(fact("parent", &["C", "E"]));
    w.run();
    let mut res = w.query(pred("grandparent", &[var("grandparent"), var("grandchild")]));
    println!("grandparents after inserting parent(C, E): {:?}", res);

    let res = res.drain(..).cloned().collect::<HashSet<_>>();
    let compared = (vec![fact("grandparent", &["A", "C"]), fact("grandparent", &["B", "D"]),
      fact("grandparent",&["B", "E"])]).drain(..).collect::<HashSet<_>>();
    assert_eq!(res, compared);

    /*w.rules.push(rule("siblings", &[var("A"), var("B")], &[
      pred("parent", &[var("parent"), var("A")]),
      pred("parent", &[var("parent"), var("B")])
    ]));

    w.run();
    println!("siblings: {:#?}", w.query(pred("siblings", &[var("A"), var("B")])));
    */
  }
}

#[cfg(test)]
mod bench {
  use super::*;
  use test::Bencher;

  #[bench]
  fn grandparents(b: &mut Bencher) {
    let mut w = World::new();
    w.facts.insert(fact("parent", &["A", "B"]));
    w.facts.insert(fact("parent", &["B", "C"]));
    w.facts.insert(fact("parent", &["C", "D"]));
    w.facts.insert(fact("parent", &["C", "E"]));
    w.facts.insert(fact("parent", &["X", "C"]));
    w.facts.insert(fact("parent", &["Y", "B"]));
    w.facts.insert(fact("parent", &["A", "0"]));
    w.facts.insert(fact("parent", &["A", "1"]));
    w.facts.insert(fact("parent", &["A", "2"]));
    w.facts.insert(fact("parent", &["A", "3"]));
    w.facts.insert(fact("parent", &["A", "4"]));

    w.facts.insert(fact("parent", &["AA", "AB"]));
    w.facts.insert(fact("parent", &["AB", "AC"]));
    w.facts.insert(fact("parent", &["AC", "AD"]));
    w.facts.insert(fact("parent", &["AC", "AE"]));
    w.facts.insert(fact("parent", &["AX", "AC"]));
    w.facts.insert(fact("parent", &["AY", "AB"]));
    w.facts.insert(fact("parent", &["AA", "0"]));
    w.facts.insert(fact("parent", &["AA", "1"]));
    w.facts.insert(fact("parent", &["AA", "2"]));
    w.facts.insert(fact("parent", &["AA", "3"]));
    w.facts.insert(fact("parent", &["AA", "4"]));

    b.iter(|| {
      w.query_rule(rule("grandparent", &[var("grandparent"), var("grandchild")], &[
        pred("parent", &[var("grandparent"), var("parent")]),
        pred("parent", &[var("parent"), var("grandchild")])
      ]))
    });
  }

}
