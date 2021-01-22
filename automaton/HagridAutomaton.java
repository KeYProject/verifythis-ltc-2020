/*
\documentclass{standalone}[12pt]

\usepackage{tikz}
\usetikzlibrary{automata}

\begin{document}

\begin{tikzpicture}[auto, ->, y=1.5cm]

  \draw[thick, rounded corners] (-3,-.5) rectangle (7.2, 3.6);

  \node[align=left] at (-1.8, 3.8) {\emph{Globals:} $\mathit{Ks} : \mathit{set}(\mathtt{String})$};

  \node[align=left, text width=2cm] at (-1.8, 2.9)
  {\emph{Locals:} \\
    $K: \mathtt{String}$ \\
    $V: \mathtt{String}$ \\
    $C: \mathtt{String}?$};
  
  \node[fill=black, circle] (empty) at (1, 3) {};
  \node[state] (registered) at (1, 2) {R};
  \node[state] (confirmed) at (1, 1) {C};
  \node[state, accepting] (finished) at (0,0) {F};

  \path
    (empty)      edge node[align=left, text width=6cm]
    {\texttt{register}(k,v)=c,  k$\not\in$Ks /\\
      V:=v; C:=c; K:=k; Ks:=Ks$\cup$\{k\}} (registered)
    (registered) edge node {\texttt{confirm}(c), c=C} (confirmed)
    (registered) edge[swap, bend right] node {\texttt{delete}(k), k=K} (finished)
    (confirmed)  edge node {\texttt{delete}(k), k=K} (finished);
\end{tikzpicture}

\end{document}
*/

// Derived ghost specification/code from this automaton

/*@ model enum State { R, C };

/*@ model class Entry {
  @  final State state;
  @  final String key;
  @  final String value;
  @  final String confirm; 
  @  Entry(...) { ... } }
  @*/

class Hagrid {

    //@ ghost \seq state;
    //@ ghost \set allKeys;

    Hagrid() {
        //@ set state = [];
        //@ set allKeys = {};
    }


    /*@ requires !(key \in allKeys);
      @*/      
    String register(String key, String value) {
        //@ ghost newEntry = new Entry(R, key, value, \result);
        //@ set state = state + [newEntry];
        //@ set allKeys = keys + {key};
    }

    /*@ forall int i; 0 <= i < state.length;
      @ requires state[i].confirm.equals(c);
      @ requires state[i].state == R;
      @*/
    void confirm(String c) {
        //@ set state[i] = new Entry(C, state[i].key, state[i].value, state.confirm);
    }

    /*@ forall int i; 0 <= i < state.length;
      @ requires state[i].key.equals(key);
      @ requires state[i].state == C;
      @ 
      @ also forall int i; 0 <= i < state.length;
      @ requires state[i].key.equals(key);
      @ requires state[i].state == R;
      @*/
    void delete(String key) {
        //@ set state = \seq_remove(state, i);
    }
}


class HagridImplementation extends Hagrid {

    // ...

    void confirm(String c) {
        // .....

        // The implementation must finish with the super-call
        // which modifies the automaton.
        super.confirm(c);
    }

}
