# Students&Companies — Software Engineering II

Requirements, design and formal modeling for a proposed platform connecting university students, companies and universities throughout the internship process. This academic project was developed for **Software Engineering II** at Politecnico di Milano in **2024–2025**.

**Authors:** [Andrea Nardi](https://github.com/NrdAnd), [Christian Giovanni Pesaturo](https://github.com/ChristianPesaturo), [Andrea Pinessi](https://github.com/AndreaPinessi).

## Project documents

| Artifact | Version and date | Contents |
| --- | --- | --- |
| [Requirement Analysis and Specification Document](DeliveryFolder/RASDv1.pdf) | 1.0 · 22 December 2024 | Goals, scope, stakeholders, scenarios, functional and quality requirements, use cases and formal analysis |
| [Design Document](DeliveryFolder/DDv1.pdf) | 1.0 · 7 January 2025 | Architecture, components, deployment and runtime views, interfaces, UI design, requirements traceability and the proposed integration and test plan |
| [Alloy model](DeliveryFolder/AlloyModel.als) | Companion source for the RASD | Signatures, relations, facts, temporal predicates, assertions and an instance-generation command |

The proposed system covers internship offers and applications, recommendations, selection, university oversight and the handling of feedback and support requests. The PDF documents specify the system and its intended implementation; the repository provides the documents and formal model.

## Explore the Alloy model

Open `DeliveryFolder/AlloyModel.als` in **Alloy Analyzer 6** and execute its `run` command. The model uses temporal constructs such as `var` and `always`. Its single `run` command requests an example containing a registered student and company. With Alloy 6.1 and the default scope, the source parses, type-checks and yields an instance.

The file also defines eight assertions, but contains no `check` commands. Finding an instance for `run` establishes satisfiability within the selected bounds; it does not establish that the assertions hold. To study an assertion, add an appropriately scoped `check` command in Alloy and examine its result.

## Repository layout

```text
.
├── README.md
├── CITATION.cff
├── LICENSE
└── DeliveryFolder/
    ├── RASDv1.pdf
    ├── DDv1.pdf
    └── AlloyModel.als
```

## Rights and citation

The Alloy source and original repository text are available under the [MIT License](LICENSE): copies or substantial portions must retain the copyright and permission notice. The two PDF deliverables retain their printed **all-rights-reserved** notices and are not licensed under MIT. University marks and other third-party material retain their own rights.

For author names and a repository citation, see [CITATION.cff](CITATION.cff).
