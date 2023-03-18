from z3 import *

# Must specify a single-tape deterministic Turing machine.


class Tm:

  def __init__(self):
    self.states = set(["s", "r00", "r11", "r01", "r10", "l", "lx", "qA", "qR"])
    self.start_state = "s"
    self.accept_state = "qA"
    self.reject_state = "qR"
    self.delta = [
      ("s", "0", "r00", "x", "R"),
      ("s", "1", "r11", "x", "R"),
      ("s", "x", "qA", "x", "R"),
      ("s", "_", "qR", "_", "R"),
      ("r00", "0", "r00", "0", "R"),
      ("r00", "1", "r01", "1", "R"),
      ("r00", "x", "lx", "x", "R"),
      ("r00", "_", "lx", "_", "L"),
      ("r01", "0", "r00", "0", "R"),
      ("r01", "1", "r01", "1", "R"),
      ("r01", "x", "qR", "1", "R"),
      ("r01", "_", "qR", "1", "R"),
      ("r10", "0", "r10", "0", "R"),
      ("r10", "1", "r11", "1", "R"),
      ("r10", "x", "qR", "1", "R"),
      ("r10", "_", "qR", "1", "R"),
      ("r11", "0", "r10", "0", "R"),
      ("r11", "1", "r11", "1", "R"),
      ("r11", "x", "lx", "x", "L"),
      ("r11", "_", "lx", "_", "L"),
      ("lx", "0", "l", "x", "L"),
      ("lx", "1", "l", "x", "L"),
      ("lx", "x", "qA", "x", "L"),
      ("lx", "_", "qR", "x", "L"),
      ("l", "0", "l", "0", "L"),
      ("l", "1", "l", "1", "L"),
      ("l", "x", "s", "x", "R"),
      ("l", "_", "qR", "x", "R"),
    ]

    self.input_alphabet = ["_", "0", "1"]
    self.tape_alphabet = ["_", "0", "1", "x"]
    self.state = None
    self.input = []


# Our verifier.
tm = Tm()

### 1. Variables ###
n = len(tm.input)

# max of p(n) time steps / tape cells
pn = 16

# The main Z3 solver object. Add constraints to this.
s = Solver()

# Q_{q,t} for each q \in Q and 0 <= t < p(n).
Q = dict()
for q in tm.states:
  Q[q] = []
  for t in range(pn):
    Q[q].append(Bool(f"{q}_{t}"))

# TODO: H_{i,t} for each 0 <= i < pn, 0 <= t < pn
H = dict()
for i in range(pn):
  H[i] = []
  for t in range(pn):
    H[i].append(Bool(f'{i}_{t}'))


# TODO: X
X = dict()
for a in tm.tape_alphabet:
  X[a] = []
  for i in range(pn):
    tmp = []
    for t in range(pn):
      tmp.append(Bool(f'{a}_{i}_{t}'))
      X[a].append(tmp)



# 1. The machine starts off in its start state.
s.add(Q[tm.start_state][0])

# TODO: 2. The head starts off at the left edge
s.add(H[0][0])

# TODO: 3. Each tape cell has some symbol in it at each point in time.
for i in range(n):
  s.add(X[tm.input[i]][i][0])


# TODO: At time 0, only input symbols allowed.

s.add(X['_'][n+1][0])

# TODO: At time 1+, any tape symbols allowed
for i in range(n+1, pn):
  for a in tm.tape_alphabet:
    s.add(X[a][i][0])


# TODO: 4. You end up in an accept state.
for t in range(pn):
  s.add(Q['qA'][t])

# TODO: Never enter a reject state
for t in range(pn):
  s.add(Not(Q['qR'][t]))


# TODO: 5. Each step of the machine is computed according to the transition.
for q in tm.states:
  for a in tm.tape_alphabet:
    for i in range(pn):
      for t in range(pn):

        # This needs to be worked on, never runs
        if q in tm.delta and a in tm.delta:
          # print(tm.delta[(q,a)])
          r, b, direction = tm.delta[(q, a)]
          # direction = tm.delta[-1]
          # Right, Left
          if direction == "R":
            s.add(Implies(And(Q[q][t], H[i][t], X[a][i][t]), And(Q[r][i+1], H[i+1][t+1], X[b][i][t+1])))
          elif direction == "L":
            s.add(Implies(And(Q[q][t], H[i][t], X[a][i][t]), And(Q[r][i+1], H[i-1][t+1], X[b][i][t+1])))


        # If the head is not in the immediate vicinity, copy.
        else:
          for j in range(pn):
            if i == j:
              continue
            # for some reason t+1 throws an error
            s.add(Implies(And(H[i][t], X[a][j][t]), X[a][j][t]))

# # TODO: 6a. If you're in one state, you're not in another.
for q in tm.states:
  for r in tm.states:
    if q == r:
      continue
    for t in range(pn):
      clause = Implies(Q[q][t], Not(Q[r][t]))
      s.add(clause)


# # TODO: 6b. If your head is somewhere, it's not somewhere else.
for i in range(pn):

  for j in range(pn):
    if i == j:
      continue
    for t in range(pn):
      s.add(Implies(H[i][t], Not(H[j][t])))



# # TODO: Head must be somewhere at each time step.
for i in range(pn):
  for t in range(pn):
    s.add(H[i][t])


# # TODO: 6c. If something is written on a tape cell, nothing else is written there.
for a in tm.tape_alphabet:
  for b in tm.tape_alphabet:
    if a == b:
      continue
    for i in range(pn):
      for t in range(pn):
        s.add(Implies(X[a][i][t], Not(X[b][i][t])))



print(s.check())
m = s.model()
print(m)

# TODO: Output# 418hw7a
