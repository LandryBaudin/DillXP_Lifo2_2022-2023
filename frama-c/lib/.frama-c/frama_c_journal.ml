(* Frama-C journal generated at 00:02 the 14/02/2023 *)

exception Unreachable
exception Exception of string

[@@@ warning "-26"]

(* Run the user commands *)
let run () =
  Dynamic.Parameter.Bool.set "-wp" true;
  Dynamic.Parameter.Bool.set "-rte" true;
  Dynamic.Parameter.String.set ""
    "/home/landry/projet_dill/lifo2/DillXP_Lifo2_2022-2023/frama-c/lib/circular-list_ll.c";
  File.init_from_cmdline ();
  !Db.RteGen.compute ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Dynamic.Parameter.Bool.clear "-wp" ();
  Project.set_keep_current false;
  Dynamic.Parameter.String.set "-wp-cache" "update";
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  Project.clear
    ~selection:(State_selection.of_list
                  [ State.get "Report.print_once";
                    State.get "Report.print_csv_once";
                    State.get "Report.classify_once";
                    State.get "Property_status.Consolidated_status";
                    State.get "PivotSourceState";
                    State.get "Consolidation graph" ])
    ();
  ()

(* Main *)
let main () =
  Journal.keep_file
     (Datatype.Filepath.of_string
     (".frama-c/frama_c_journal.ml"));
  try run ()
  with
  | Unreachable -> Kernel.fatal "Journal reaches an assumed dead code" 
  | Exception s -> Kernel.log "Journal re-raised the exception %S" s
  | exn ->
    Kernel.fatal
      "Journal raised an unexpected exception: %s"
      (Printexc.to_string exn)

(* Registering *)
let main : unit -> unit =
  Dynamic.register
    ~plugin:"Frama_c_journal.ml"
    "main"
    (Datatype.func Datatype.unit Datatype.unit)
    ~journalize:false
    main

(* Hooking *)
let () = Cmdline.run_after_loading_stage main; Cmdline.is_going_to_load ()
