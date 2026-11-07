import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 392 of the cap-17 certificate: slots 200704 .. 201215 -/
theorem chk_392 : chunkCheck 17 T stdSt 200704 512 = true := by decide +kernel

end Row17
