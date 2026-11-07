import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 83 of the cap-16 certificate: slots 84992 .. 86015 -/
theorem chk_83 : chunkCheck 16 T stdSt 84992 1024 = true := by decide +kernel

end Row16
