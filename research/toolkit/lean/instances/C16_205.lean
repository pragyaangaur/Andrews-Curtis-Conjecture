import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 205 of the cap-16 certificate: slots 209920 .. 210943 -/
theorem chk_205 : chunkCheck 16 T stdSt 209920 1024 = true := by decide +kernel

end Row16
