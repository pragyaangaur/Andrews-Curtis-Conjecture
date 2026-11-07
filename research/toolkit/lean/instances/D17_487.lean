import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 487 of the cap-17 certificate: slots 249344 .. 249855 -/
theorem chk_487 : chunkCheck 17 T stdSt 249344 512 = true := by decide +kernel

end Row17
