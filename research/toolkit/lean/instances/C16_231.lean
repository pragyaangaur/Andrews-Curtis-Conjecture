import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 231 of the cap-16 certificate: slots 236544 .. 237567 -/
theorem chk_231 : chunkCheck 16 T stdSt 236544 1024 = true := by decide +kernel

end Row16
