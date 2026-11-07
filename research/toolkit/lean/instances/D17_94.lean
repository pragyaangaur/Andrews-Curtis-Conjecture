import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 94 of the cap-17 certificate: slots 48128 .. 48639 -/
theorem chk_94 : chunkCheck 17 T stdSt 48128 512 = true := by decide +kernel

end Row17
