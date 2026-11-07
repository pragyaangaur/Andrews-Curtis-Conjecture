import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 99 of the cap-16 certificate: slots 101376 .. 102399 -/
theorem chk_99 : chunkCheck 16 T stdSt 101376 1024 = true := by decide +kernel

end Row16
