import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 83 of the cap-17 certificate: slots 42496 .. 43007 -/
theorem chk_83 : chunkCheck 17 T stdSt 42496 512 = true := by decide +kernel

end Row17
