import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 170 of the cap-16 certificate: slots 174080 .. 175103 -/
theorem chk_170 : chunkCheck 16 T stdSt 174080 1024 = true := by decide +kernel

end Row16
