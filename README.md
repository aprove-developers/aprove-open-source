# 🔎 AProVE — Automated Program Verification Environment

<p align="center">
  <img src="Images/aprove_logo_new.png" alt="AProVE logo" width="420" />
</p>

<p align="center"><strong>Automated reasoning about program termination and complexity</strong></p>

<p align="center">
  <a href="https://github.com/aprove-developers/aprove-open-source/releases">Releases</a>
  ·
  <a href="https://github.com/aprove-developers/aprove-open-source/wiki">Developer Guide</a>
  ·
  <a href="https://github.com/aprove-developers/aprove-open-source/issues">Issues</a>
  ·
  <a href="http://www.youtube.com/watch?v=-OrJi9DeKOg">Intro Video</a>
</p>

<p align="center"><em>Current release: 1.0.0 Capybara</em></p>

---

## 📖 Overview

AProVE is an automated verification framework for proving properties such as termination and worst-case complexity. It is developed by the <a href="https://verify.rwth-aachen.de/index.html#research">Programming Languages and Verification</a> group at RWTH Aachen University.

At a high level, AProVE helps answer questions like:

- Does this program terminate on all inputs?
- How time consuming can its execution become in the worst case?
- Can these properties be derived automatically from a formal model of the program?

AProVE supports several programming paradigms and input languages, including rewriting-based, imperative, functional, and logic-oriented formalisms. Instead of relying on testing alone, it builds machine-checkable proof obligations and solves them with formal methods.

## 📖 Why AProVE

| Capability | Description |
| --- | --- |
| Termination analysis | Proves whether a program always terminates |
| Complexity analysis | Derives lower and upper bounds on runtime |
| Multiple formalisms | Supports languages such as Java, C, Haskell, and Prolog |
| Extensible architecture | New processors, strategies, and backends can be integrated |

## 🧠 How It Works

AProVE follows a <b>transform-and-analyze</b> approach:

1. Translate the input program into an internal problem representation.
2. Apply processors that simplify, decompose, or solve the problem.
3. Use strategies to orchestrate the analysis flow.
4. Delegate specialized proof obligations to backend solvers.
5. Combine all intermediate results into a final result.

Typical outcomes include `YES`, `NO`, and `MAYBE` for termination, as well as complexity bounds such as `O(1)`, `O(n)`, or `EXP`.

## 🏗️ Architecture

The core system is organized around four concepts.

### Problems

A problem captures the current analysis state. For example, a term rewrite system may be represented as a `TRSProblem`.

### Processors

Processors are the main transformation units in AProVE. They either simplify a problem, split it into subproblems, or solve it directly.

### Strategies

Strategies control which processors are applied, in which order, and under which conditions.

### Solvers

Solvers handle specific mathematical subproblems. AProVE integrates backend technologies such as SAT and SMT solvers, as well as domain-specific tools like KoAT for complexity analysis.

## 🎥 Project Resources

### Video Introduction

<p align="center">
  <a href="http://www.youtube.com/watch?v=-OrJi9DeKOg">
    <img src="Images/AProVE_Youtube.png" alt="AProVE introduction video" width="420" />
  </a>
</p>

### Development Setup

For local development and build instructions, see the project wiki:

<a href="https://github.com/aprove-developers/aprove-open-source/wiki">https://github.com/aprove-developers/aprove-open-source/wiki</a>

### Contributing

Contributions are welcome. AProVE is particularly well suited for extending:

- supported input languages and problem representations
- analysis processors and strategies
- solver integrations and backend tooling

If you plan to contribute code, start with the wiki and the existing architecture sections above so you can place new work into the right abstraction layer.

## 🤝 Community And Project Links

- Releases: <a href="https://github.com/aprove-developers/aprove-open-source/releases">GitHub Releases</a>
- Issues: <a href="https://github.com/aprove-developers/aprove-open-source/issues">Bug reports and feature requests</a>
- Discussions: <a href="https://github.com/aprove-developers/aprove-open-source/discussions">Community discussions</a>
- Code of Conduct: <a href="https://github.com/aprove-developers/aprove-open-source/blob/main/CODE_OF_CONDUCT.md">CODE_OF_CONDUCT.md</a>
- Contributing Guide: <a href="https://github.com/aprove-developers/aprove-open-source/blob/main/CONTRIBUTING.md">CONTRIBUTING.md</a>
