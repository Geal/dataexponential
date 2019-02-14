use super::*;

impl World {
  pub fn biscuit_create(table: &mut SymbolTable,
    mut authority_facts: Vec<Fact>, mut authority_rules: Vec<Rule>,
    mut ambient_facts: Vec<Fact>, mut ambient_rules: Vec<Rule>) -> World {
    let mut w = World::new();
    let authority_index = table.insert("authority");
    let ambient_index = table.insert("ambient");

    for fact in authority_facts.drain(..) {
      if fact.0.ids[0] != ID::Symbol(authority_index) {
        panic!("invalid authority facts");
      }

      w.facts.insert(fact);
    }

    for rule in authority_rules.drain(..) {
      w.rules.push(rule);
    }

    w.run();

    if w.facts.iter().find(|fact| fact.0.ids[0] != ID::Symbol(authority_index)).is_some() {
      panic!("generated authority facts should have the authority context");
    }

    //remove authority rules: we cannot create facts anymore in authority scope
    w.rules.clear();

    for fact in ambient_facts.drain(..) {
      if fact.0.ids[0] != ID::Symbol(ambient_index) {
        panic!("invalid ambient facts");
      }

      w.facts.insert(fact);
    }

    for rule in ambient_rules.drain(..) {
      w.rules.push(rule);
    }

    w.run();

    w
  }

  pub fn biscuit_add_fact(&mut self, authority_index: u64, ambient_index: u64, fact: Fact) {
    if fact.0.ids[0] == ID::Symbol(authority_index)
      || fact.0.ids[0] == ID::Symbol(ambient_index) {
      panic!("block facts cannot add to authority or ambient contexts");
    }

    self.facts.insert(fact);
  }

  pub fn biscuit_add_rule(&mut self, rule: Rule) {
    self.rules.push(rule);
  }

  pub fn biscuit_run(&mut self, authority_index: u64, ambient_index: u64) {
    let mut index = 0;
    loop {
      let mut new_facts:Vec<Fact> = Vec::new();
      for rule in self.rules.iter() {
        rule.apply(&self.facts, &mut new_facts);
      }

      let len = self.facts.len();

      for fact in new_facts.iter() {
        if fact.0.ids[0] == ID::Symbol(authority_index)
          || fact.0.ids[0] == ID::Symbol(ambient_index) {
          panic!("block rules should not generate authority or ambient facts");
        }
      }

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
}

#[cfg(test)]
mod tests {
  use super::*;
  use super::super::*;

  #[test]
  fn biscuit() {
    let mut syms = SymbolTable::new();
    let authority = syms.insert("authority");
    let ambient = syms.insert("ambient");

    let authority_facts = vec![
      fact("right", &[ID::Symbol(authority), sym(&mut syms, "file1"), sym(&mut syms, "read")]),
      fact("right", &[ID::Symbol(authority), sym(&mut syms, "file2"), sym(&mut syms, "read")]),
      fact("right", &[ID::Symbol(authority), sym(&mut syms, "file1"), sym(&mut syms, "write")]),
    ];
    let authority_rules = Vec::new();
    let ambient_facts = vec![
      fact("resource", &[ID::Symbol(ambient), sym(&mut syms, "file1")]),
      fact("operation", &[ID::Symbol(ambient), sym(&mut syms, "read")]),
    ];
    let ambient_rules = Vec::new();

    let mut w = World::biscuit_create(&mut syms, authority_facts, authority_rules,
      ambient_facts, ambient_rules);

    let res = w.query_rule(rule("caveat1", &[], &[
      pred("resource", &[ID::Symbol(ambient), var("X")]),
      pred("operation", &[ID::Symbol(ambient), sym(&mut syms, "read")]),
      pred("right", &[ID::Symbol(authority), var("X"), sym(&mut syms, "read")])
    ]));

    println!("caveat 1 results:");
    for fact in res.iter() {
      println!("\t{}", syms.print_fact(fact));
    }

    assert!(!res.is_empty());
  }
}
