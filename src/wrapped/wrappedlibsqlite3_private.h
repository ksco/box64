#if !(defined(GO) && defined(GOM) && defined(GO2) && defined(DATA))
error Meh...
#endif

GO(sqlite3_aggregate_context, pFpi)
GO(sqlite3_aggregate_count, iFp)
// GO(sqlite3_auto_extension, 
GO(sqlite3_backup_finish, iFp)
GO(sqlite3_backup_init, pFpppp)
// GO(sqlite3_backup_pagecount, iFp)
GO(sqlite3_backup_step, iFpi)
// GO(sqlite3_bind_blob, 
// GO(sqlite3_bind_blob64, 
GO(sqlite3_bind_double, iFpid)
GO(sqlite3_bind_int, iFpii)
GO(sqlite3_bind_int64, iFpiI)
GO(sqlite3_bind_null, iFpi)
GO(sqlite3_bind_parameter_count, iFp)
GO(sqlite3_bind_parameter_index, iFpp)
GO(sqlite3_bind_parameter_name, pFpi)
// GO(sqlite3_bind_pointer, 
// GO(sqlite3_bind_text, 
// GO(sqlite3_bind_text16, 
// GO(sqlite3_bind_text64, 
GO(sqlite3_bind_value, iFpip)
GO(sqlite3_bind_zeroblob, iFpii)
GO(sqlite3_bind_zeroblob64, iFpiU)
GO(sqlite3_blob_bytes, iFp)
GO(sqlite3_blob_close, iFp)
GO(sqlite3_blob_open, iFppppIip)
GO(sqlite3_blob_read, iFppii)
GO(sqlite3_blob_write, iFppii)
// GO(sqlite3_busy_handler, 
GO(sqlite3_busy_timeout, iFpi)
// GO(sqlite3_cancel_auto_extension, 
GO(sqlite3_changes, iFp)
GO(sqlite3_clear_bindings, iFp)
GO(sqlite3_close_v2, iFp)
GO(sqlite3_close, iFp)
// GO(sqlite3_collation_needed, 
// GO(sqlite3_collation_needed16, 
GO(sqlite3_column_blob, pFpi)
GO(sqlite3_column_bytes, iFpi)
GO(sqlite3_column_count, iFp)
GO(sqlite3_column_database_name, pFpi)
GO(sqlite3_column_database_name16, pFpi)
GO(sqlite3_column_decltype, pFpi)
GO(sqlite3_column_decltype16, pFpi)
GO(sqlite3_column_double, dFpi)
GO(sqlite3_column_int, iFpi)
GO(sqlite3_column_int64, IFpi)
GO(sqlite3_column_name, pFpi)
GO(sqlite3_column_name16, pFpi)
GO(sqlite3_column_origin_name, pFpi)
GO(sqlite3_column_origin_name16, pFpi)
GO(sqlite3_column_table_name, pFpi)
GO(sqlite3_column_table_name16, pFpi)
GO(sqlite3_column_text16, pFpi)
GO(sqlite3_column_type, iFpi)
GO(sqlite3_column_value, pFpi)
// GO(sqlite3_commit_hook, 
GO(sqlite3_compileoption_get, pFi)
GO(sqlite3_compileoption_used, iFp)
GO(sqlite3_complete, iFp)
GO(sqlite3_complete16, iFp)
// GO(sqlite3_config, 
GO(sqlite3_context_db_handle, pFp)
// GO(sqlite3_create_collation_v2, 
// GO(sqlite3_create_collation, 
// GO(sqlite3_create_collation16, 
GO(sqlite3_create_filename, pFpppip)
// GO(sqlite3_create_function_v2, 
// GO(sqlite3_create_function, 
// GO(sqlite3_create_function16, 
// GO(sqlite3_create_module_v2, 
// GO(sqlite3_create_module, 
// GO(sqlite3_create_window_function, 
GO(sqlite3_data_count, iFp)
// GO(sqlite3_data_directory, 
GO(sqlite3_database_file_object, pFp)
GO(sqlite3_db_cacheflush, iFp)
// GO(sqlite3_db_config, 
GO(sqlite3_db_filename, pFpp)
GO(sqlite3_db_handle, pFp)
GO(sqlite3_db_mutex, pFp)
GO(sqlite3_db_readonly, iFpp)
GO(sqlite3_db_release_memory, iFp)
GO(sqlite3_db_status, iFpippi)
GO(sqlite3_declare_vtab, iFpp)
GO(sqlite3_enable_load_extension, iFpi)
GO(sqlite3_enable_shared_cache, iFi)
GO(sqlite3_errcode, iFp)
GO(sqlite3_errmsg, pFp)
GO(sqlite3_errmsg16, pFp)
GO(sqlite3_errstr, pFi)
GOM(sqlite3_exec, iFEppppp)
GO(sqlite3_expanded_sql, pFp)
GO(sqlite3_extended_errcode, iFp)
GO(sqlite3_extended_result_codes, iFpi)
GO(sqlite3_file_control, iFppip)
GO(sqlite3_filename_database, pFp)
GO(sqlite3_filename_journal, pFp)
GO(sqlite3_filename_wal, pFp)
GO(sqlite3_finalize, iFp)
GO(sqlite3_free_filename, vFp)
GO(sqlite3_free_table, vFp)
GO(sqlite3_free, vFp)
GO(sqlite3_get_autocommit, iFp)
GO(sqlite3_get_auxdata, pFpi)
GO(sqlite3_get_table, iFpppppp)
GO(sqlite3_global_recover, iFv)
GO(sqlite3_hard_heap_limit64, IFI)
GO(sqlite3_initialize, iFv)
GO(sqlite3_interrupt, vFp)
GO(sqlite3_keyword_check, iFpi)
GO(sqlite3_keyword_count, iFv)
GO(sqlite3_keyword_name, iFipp)
GO(sqlite3_last_insert_rowid, IFp)
GO(sqlite3_libversion_number, iFv)
GO(sqlite3_libversion, pFv)
GO(sqlite3_limit, iFpii)
GO(sqlite3_load_extension, iFpppp)
// GO(sqlite3_log, 
GO(sqlite3_malloc, pFi)
GO(sqlite3_malloc64, pFU)
// GO(sqlite3_memory_alarm, 
GO(sqlite3_memory_highwater, IFi)
GO(sqlite3_memory_used, IFv)
// GO(sqlite3_mprintf, 
GO(sqlite3_msize, UFp)
GO(sqlite3_mutex_alloc, pFi)
GO(sqlite3_mutex_enter, vFp)
GO(sqlite3_mutex_free, vFp)
GO(sqlite3_mutex_try, iFp)
GO(sqlite3_next_stmt, pFpp)
GO(sqlite3_open_v2, iFppip)
GO(sqlite3_open16, iFpp)
GO(sqlite3_os_end, iFv)
GO(sqlite3_os_init, iFv)
GO(sqlite3_overload_function, iFppi)
GO(sqlite3_prepare_v2, iFppipp)
GO(sqlite3_prepare_v3, iFppippp)
GO(sqlite3_prepare16_v2, iFppipp)
GO(sqlite3_prepare16_v3, iFppippp)
GO(sqlite3_prepare16, iFppipp)
// GO(sqlite3_profile, 
// GO(sqlite3_progress_handler, 
GO(sqlite3_randomness, vFip)
GO(sqlite3_realloc, pFpi)
GO(sqlite3_realloc64, pFpU)
GO(sqlite3_release_memory, iFi)
GO(sqlite3_reset_auto_extension, vFv)
GO(sqlite3_reset, iFp)
// GO(sqlite3_result_blob, 
// GO(sqlite3_result_blob64, 
GO(sqlite3_result_error_code, vFpi)
GO(sqlite3_result_error_nomem, vFp)
GO(sqlite3_result_error_toobig, vFp)
GO(sqlite3_result_error, vFppi)
GO(sqlite3_result_error16, vFppi)
GO(sqlite3_result_int, vFpi)
GO(sqlite3_result_int64, vFpI)
GO(sqlite3_result_null, vFp)
// GO(sqlite3_result_pointer, 
GO(sqlite3_result_subtype, vFpu)
// GO(sqlite3_result_text, 
// GO(sqlite3_result_text16, 
// GO(sqlite3_result_text16be, 
// GO(sqlite3_result_text16le, 
// GO(sqlite3_result_text64, 
GO(sqlite3_result_value, vFpp)
GO(sqlite3_result_zeroblob, vFpi)
GO(sqlite3_result_zeroblob64, iFpU)
// GO(sqlite3_rollback_hook, 
// GO(sqlite3_rtree_geometry_callback, 
// GO(sqlite3_rtree_query_callback, 
// GO(sqlite3_set_authorizer, 
// GO(sqlite3_set_auxdata, 
// GO(sqlite3_set_last_insert_rowid, 
GO(sqlite3_shutdown, iFv)
GO(sqlite3_sleep, iFi)
// GO(sqlite3_snprintf, 
GO(sqlite3_soft_heap_limit, vFi)
GO(sqlite3_soft_heap_limit64, IFI)
GO(sqlite3_sourceid, pFv)
GO(sqlite3_sql, pFp)
GO(sqlite3_status, iFippi)
GO(sqlite3_status64, iFippi)
GO(sqlite3_step, iFp)
GO(sqlite3_stmt_busy, iFp)
GO(sqlite3_stmt_isexplain, iFp)
GO(sqlite3_stmt_readonly, iFp)
GO(sqlite3_stmt_status, iFpii)
GO(sqlite3_str_append, vFppi)
GO(sqlite3_str_appendall, vFpp)
GO(sqlite3_str_appendchar, vFpic)
// GO(sqlite3_str_appendf, 
GO(sqlite3_str_errcode, iFp)
GO(sqlite3_str_finish, pFp)
GO(sqlite3_str_length, iFp)
GO(sqlite3_str_new, pFp)
GO(sqlite3_str_reset, vFp)
GO(sqlite3_str_value, pFp)
// GO(sqlite3_str_vappendf, 
GO(sqlite3_strglob, iFpp)
GO(sqlite3_stricmp, iFpp)
GO(sqlite3_strlike, iFppu)
GO(sqlite3_strnicmp, iFppi)
GO(sqlite3_system_errno, iFp)
// GO(sqlite3_table_column_metadata, 
// GO(sqlite3_temp_directory, 
// GO(sqlite3_test_control, 
// GO(sqlite3_thread_cleanup, 
// GO(sqlite3_threadsafe, 
// GO(sqlite3_total_changes, 
// GO(sqlite3_trace_v2, 
// GO(sqlite3_trace, 
// GO(sqlite3_transfer_bindings, 
// GO(sqlite3_txn_state, 
// GO(sqlite3_unlock_notify, 
// GO(sqlite3_unsupported_selecttrace, 
// GO(sqlite3_update_hook, 
GO(sqlite3_uri_boolean, iFppi)
GO(sqlite3_uri_int64, IFppI)
GO(sqlite3_uri_key, pFpi)
GO(sqlite3_uri_parameter, pFpp)
// GO(sqlite3_user_data, 
GO(sqlite3_value_blob, pFp)
GO(sqlite3_value_bytes, iFp)
GO(sqlite3_value_bytes16, iFp)
GO(sqlite3_value_double, dFp)
GO(sqlite3_value_dup, pFp)
GO(sqlite3_value_free, vFp)
GO(sqlite3_value_frombind, iFp)
GO(sqlite3_value_int, iFp)
GO(sqlite3_value_int64, IFp)
GO(sqlite3_value_nochange, iFp)
GO(sqlite3_value_numeric_type, iFp)
GO(sqlite3_value_subtype, uFp)
GO(sqlite3_value_text, pFp)
GO(sqlite3_value_text16, pFp)
GO(sqlite3_value_text16be, pFp)
GO(sqlite3_value_text16le, pFp)
GO(sqlite3_value_type, iFp)
// GO(sqlite3_version, 
// GO(sqlite3_vfs_find, 
// GO(sqlite3_vfs_register, 
// GO(sqlite3_vfs_unregister, 
// GO(sqlite3_vmprintf, 
// GO(sqlite3_vsnprintf, 
// GO(sqlite3_vtab_collation, 
// GO(sqlite3_vtab_config, 
// GO(sqlite3_vtab_nochange, 
// GO(sqlite3_vtab_on_conflict, 
// GO(sqlite3_wal_autocheckpoint, 
GO(sqlite3_wal_checkpoint_v2, iFppipp)
GO(sqlite3_wal_checkpoint, iFpp)
// GO(sqlite3_wal_hook, 
GO(sqlite3_backup_remaining, iFp)
GO(sqlite3_blob_reopen, iFpI)
GO(sqlite3_column_bytes16, iFpi)
GO(sqlite3_column_text, pFpi)
GO(sqlite3_drop_modules, iFpp)
GO(sqlite3_expired, iFp)
GO(sqlite3_mutex_leave, vFp)
GO(sqlite3_open, iFpp)
GO(sqlite3_prepare, iFppipp)
GO(sqlite3_result_double, vFpd)
GO(sqlite3_value_pointer, pFpp)
