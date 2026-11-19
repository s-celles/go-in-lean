// Progressive enhancement for the History charts: a crosshair and a tooltip with
// every series at the nearest day. Each chart's values stay in its data table.
document.addEventListener("DOMContentLoaded", () => {
  document.querySelectorAll("figure.hchart[data-chart]").forEach(figure => {
    const data = JSON.parse(figure.dataset.chart);
    const svg = figure.querySelector("svg");
    const cross = svg.querySelector(".hchart-cross");
    const tip = figure.querySelector(".hchart-tip");
    const lines = [...svg.querySelectorAll(".hchart-line")];
    const xs = lines.length ? lines[0].getAttribute("points").split(" ").map(p => parseFloat(p)) : [];
    if (!xs.length) return;
    let index = xs.length - 1;
    const show = i => {
      index = Math.max(0, Math.min(xs.length - 1, i));
      cross.setAttribute("x1", xs[index]);
      cross.setAttribute("x2", xs[index]);
      cross.setAttribute("visibility", "visible");
      tip.replaceChildren();
      const date = document.createElement("div");
      date.className = "date";
      date.textContent = data.dates[index];
      tip.append(date);
      data.series.forEach((s, k) => {
        const row = document.createElement("div");
        row.className = "row";
        const key = document.createElement("span");
        key.className = `hchart-key hchart-s${k + 1}`;
        const value = document.createElement("strong");
        value.textContent = s.Values[index].toLocaleString("en");
        const name = document.createElement("span");
        name.className = "name";
        name.textContent = s.Name;
        row.append(key, value, name);
        tip.append(row);
      });
      tip.hidden = false;
      const box = svg.getBoundingClientRect(), fig = figure.getBoundingClientRect();
      const scale = box.width / svg.viewBox.baseVal.width;
      const px = box.left - fig.left + xs[index] * scale;
      const left = px + 12 + tip.offsetWidth > fig.width ? px - 12 - tip.offsetWidth : px + 12;
      tip.style.left = `${Math.max(0, left)}px`;
      tip.style.top = `${box.top - fig.top + 8}px`;
    };
    const hide = () => { cross.setAttribute("visibility", "hidden"); tip.hidden = true; };
    const nearest = event => {
      const box = svg.getBoundingClientRect();
      const x = (event.clientX - box.left) * svg.viewBox.baseVal.width / box.width;
      let best = 0;
      xs.forEach((v, i) => { if (Math.abs(v - x) < Math.abs(xs[best] - x)) best = i; });
      return best;
    };
    svg.addEventListener("pointermove", event => show(nearest(event)));
    svg.addEventListener("pointerleave", hide);
    figure.tabIndex = 0;
    figure.addEventListener("focus", () => show(index));
    figure.addEventListener("blur", hide);
    figure.addEventListener("keydown", event => {
      if (event.key === "ArrowLeft") { show(index - 1); event.preventDefault(); }
      if (event.key === "ArrowRight") { show(index + 1); event.preventDefault(); }
      if (event.key === "Escape") hide();
    });
  });
});
