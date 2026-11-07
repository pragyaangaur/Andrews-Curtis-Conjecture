import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 184 of the cap-16 certificate: slots 188416 .. 189439 -/
theorem chk_184 : chunkCheck 16 T stdSt 188416 1024 = true := by decide +kernel

end Row16
