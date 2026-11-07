import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 89 of the cap-17 certificate: slots 45568 .. 46079 -/
theorem chk_89 : chunkCheck 17 T stdSt 45568 512 = true := by decide +kernel

end Row17
