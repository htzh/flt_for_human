## HTML Docs Generation

The project generates indices and documentation **entirely through filename and filesystem conventions**, without running the Lean compiler. The [README](https://github.com/anthropics/fermats-last-theorem/blob/main/tools/docs-site/README.md) explicitly states:

> "*Nothing here runs Lean; the .lean files are read as text.*"

Here is how the system uses conventions instead of Lean artifacts:

### 📁 **Filesystem Structure as Source of Truth**
The generator expects a specific repository layout to discover content:
*   **`Theorems/`** – Contains theorem files.
*   **`P2M/Sol/`** – Contains solution files.
*   **`Definitions/`** – Contains definition files.
*   **`README.md`**, **`PROOF-PATH.md`**, **`ATTRIBUTION.md`** – Root-level markdown documents.
*   **`lean-toolchain`** – Identifies the Lean version (used as metadata, not for compilation).

### 🗂️ **Document Discovery by Naming**
The system builds its indices based on these conventions:
*   **Theorems and Definitions**: Each `.lean` file in the `Theorems/`, `P2M/Sol/`, and `Definitions/` folders becomes a separate page. The page title and navigation structure are derived from the **file path and name**.
*   **Route and Chapters**: The required `route.md` file (from `--docs`) defines the narrative chapters and selects which theorems appear as "landmarks." The `--docs` folder can also include optional prose documents like `overview.md`, `structure.md`, etc., which are rendered as separate pages under the "Documents" section.
*   **Cross-linking**: The generator parses the `.lean` files as **plain text** to find citations (e.g., references to other theorem or definition names). It counts how often each name appears to build the citation graph and cross-links.

### ⚙️ **Data Augmentation (Optional, Not Required)**
You can provide additional metadata via the `--content` folder (e.g., English titles, statements, proof ideas in `.json`/`.jsonl` files). This data is **keyed by the Lean name** (which matches the filename/definition name). If not provided, the pages still render, just with less descriptive text.

### 💡 **Practical Implication**
This design means you can:
1.  **Generate the site from a source checkout** without having Lean installed.
2.  **Rely on file paths** to organize the documentation hierarchy.
3.  **Add new theorems** simply by creating new `.lean` files in the appropriate folders—the generator will automatically include them on the next run.

In summary, the project successfully decouples documentation generation from Lean compilation by using the **file system and naming conventions** as the primary organizational and discovery mechanism.
