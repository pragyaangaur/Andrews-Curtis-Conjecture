import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 135 of the cap-16 certificate: slots 138240 .. 139263 -/
theorem chk_135 : chunkCheck 16 T stdSt 138240 1024 = true := by decide +kernel

end Row16
