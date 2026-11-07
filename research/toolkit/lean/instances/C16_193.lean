import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 193 of the cap-16 certificate: slots 197632 .. 198655 -/
theorem chk_193 : chunkCheck 16 T stdSt 197632 1024 = true := by decide +kernel

end Row16
