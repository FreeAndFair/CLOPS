package ie.ucd.clops.runtime.automaton;

import java.util.Set;

import ie.ucd.clops.runtime.options.IMatchable;

/** 
  Builds a full automaton for static checks. 
 */
public class BigAutomatonMaker {
  private Automaton<IMatchable> parsingAutomaton;
  private dk.brics.automaton.Automaton bigAutomaton;
  private Set<dk.brics.automaton.State> blackStates;

  public BigAutomatonMaker(Automaton<IMatchable> parsingAutomaton) {
    this.parsingAutomaton = parsingAutomaton;
  }

  public dk.brics.automaton.Automaton getAutomaton() {
    if (bigAutomaton == null) {
      build();
    }
    return bigAutomaton;
  }

  public Set<dk.brics.automaton.State> getBlackStates() { 
    if (bigAutomaton == null) {
      build();
    }
    return blackStates;
  }

  private void build() {
    
  }
}
