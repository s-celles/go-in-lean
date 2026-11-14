// Progressive enhancement: the complete registry remains readable without JavaScript.
document.addEventListener("DOMContentLoaded", () => {
  const controls = document.querySelector("[data-registry-controls]");
  if (!controls) return;
  const content = controls.closest(".content");
  const tables = [...content.querySelectorAll("table")];
  const rows = tables.flatMap(table => [...table.querySelectorAll("tbody tr")]);
  const input = controls.querySelector("input");
  const count = controls.querySelector("[data-registry-count]");
  const update = () => {
    const terms = input.value.toLocaleLowerCase().trim().split(/\s+/).filter(Boolean);
    let visible = 0;
    rows.forEach(row => {
      const text = row.textContent.toLocaleLowerCase();
      row.hidden = !terms.every(term => text.includes(term));
      if (!row.hidden) visible++;
    });
    count.textContent = `${visible} of ${rows.length} rows shown`;
  };
  input.addEventListener("input", update);
  const collator = new Intl.Collator("en", { numeric: true, sensitivity: "base" });
  tables.forEach(table => {
    table.querySelectorAll("thead th").forEach((heading, column) => {
      const button = document.createElement("button");
      button.type = "button";
      button.className = "registry-sort";
      button.textContent = heading.textContent.trim() + " ↕";
      button.setAttribute("aria-label", `Sort by ${heading.textContent.trim()}`);
      heading.textContent = "";
      heading.append(button);
      button.addEventListener("click", () => {
        const descending = heading.getAttribute("aria-sort") === "ascending";
        table.querySelectorAll("thead th").forEach(th => th.removeAttribute("aria-sort"));
        heading.setAttribute("aria-sort", descending ? "descending" : "ascending");
        const body = table.querySelector("tbody");
        [...body.rows].sort((a, b) => {
          const order = collator.compare(a.cells[column].textContent.trim(), b.cells[column].textContent.trim());
          return descending ? -order : order;
        }).forEach(row => body.append(row));
      });
    });
  });
  update();
});
