# Deligne–Serre port — friction log

Records the deviations made during the forward port (the phase order is
[../topics/deligneSerre/TOPIC-port-order.md](../topics/deligneSerre/TOPIC-port-order.md)
§2): things resolved *locally* because promoting them would have re-opened a
**closed** file. The periodic **refactor round** reads this file, promotes the
entries into their homes, and updates the importers.

Entry format:

```text
## <date>  <file being written>
- wanted: <declaration / block>
  home it belongs in: <module>
  currently: <closed file it lives in / not ported / pin-only>
  local workaround: <private copy name / local restatement, + lines>
  why not resolved here: <closed importee / needs an existing file touched>
```

One entry per missed share. Keep it honest: the point is that the promotion
happens in a dedicated round, not mid-port.

---

_(no entries yet — the port has not started)_
