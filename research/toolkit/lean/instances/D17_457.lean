import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 457 of the cap-17 certificate: slots 233984 .. 234495 -/
theorem chk_457 : chunkCheck 17 T stdSt 233984 512 = true := by decide +kernel

end Row17
