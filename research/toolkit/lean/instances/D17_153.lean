import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 153 of the cap-17 certificate: slots 78336 .. 78847 -/
theorem chk_153 : chunkCheck 17 T stdSt 78336 512 = true := by decide +kernel

end Row17
