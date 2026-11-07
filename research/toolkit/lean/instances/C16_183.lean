import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 183 of the cap-16 certificate: slots 187392 .. 188415 -/
theorem chk_183 : chunkCheck 16 T stdSt 187392 1024 = true := by decide +kernel

end Row16
